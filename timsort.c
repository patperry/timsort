/*
 * Copyright (C) 2011 Patrick O. Perry
 * Copyright (C) 2008 The Android Open Source Project
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

#include <assert.h>		// assert
#include <errno.h>		// EINVAL
#include <stddef.h>		// size_t, NULL
#include <stdint.h>		// SIZE_MAX
#include <stdlib.h>		// malloc, realloc, free
#include <string.h>		// memcpy, memmove
#include "timsort.h"

/**
 * This is the minimum sized sequence that will be merged.  Shorter
 * sequences will be lengthened by calling binarySort.  If the entire
 * array is less than this length, no merges will be performed.
 *
 * This constant should be a power of two.  It was 64 in Tim Peter's C
 * implementation, but 32 was empirically determined to work better in
 * [Android's Java] implementation.  In the unlikely event that you set
 * this constant to be a number that's not a power of two, you'll need
 * to change the {@link #minRunLength} computation.
 *
 * If you decrease this constant, you must change the stackLen
 * computation in the TimSort constructor, or you risk an
 * ArrayOutOfBounds exception.  See listsort.txt for a discussion
 * of the minimum stack length required as a function of the length
 * of the array being sorted and the minimum merge sequence length.
 */
#define MIN_MERGE 32

/**
 * When we get into galloping mode, we stay there until both runs win less
 * often than MIN_GALLOP consecutive times.
 */
#define MIN_GALLOP 7

/**
 * Maximum initial size of tmp array, which is used for merging.  The array
 * can grow to accommodate demand.
 *
 * Unlike Tim's original C version, we do not allocate this much storage
 * when sorting smaller arrays.  This change was required for performance.
 */
#define INITIAL_TMP_STORAGE_LENGTH 256

typedef int (*comparator) (const void *x, const void *y, void *udata);

#define ELEM(a,i) ((char *)(a) + (i) * width)

#define MIN(a,b) ((a) <= (b) ? (a) : (b))

#define SUCCESS 0
#define FAILURE (-1)

struct timsort {
	/**
	 * The array being sorted.
	 */
	void *a;
	size_t a_length;
	size_t width;

	/**
	 * The comparator for this sort.
	 */
	int (*c) (const void *x, const void *y, void *udata);
	void *udata;

	/**
	 * This controls when we get *into* galloping mode.  It is initialized
	 * to MIN_GALLOP.  The mergeLo and mergeHi methods nudge it higher for
	 * random data, and lower for highly structured data.
	 */
	int minGallop;

	/**
	 * Temp storage for merges.
	 */
	void *tmp;
	size_t tmp_length;

	/**
	 * A stack of pending runs yet to be merged.  Run i starts at
	 * address base[i] and extends for len[i] elements.  It's always
	 * true (so long as the indices are in bounds) that:
	 *
	 *     runBase[i] + runLen[i] == runBase[i + 1]
	 *
	 * so we could cut the storage for this, but it's a minor amount,
	 * and keeping all the info explicit simplifies the code.
	 */
	size_t stackSize;	// Number of pending runs on stack
	void **runBase;
	size_t *runLen;
};

static void binarySort(void *a, size_t hi, size_t start,
		       comparator compare, void *udata, size_t width);
static size_t countRunAndMakeAscending(void *a, size_t hi,
				       comparator compare, void *udata,
				       size_t width);
static void reverseRange(void *a, size_t lo, size_t hi, size_t width);
static size_t minRunLength(size_t n);
static void pushRun(struct timsort *ts, void *runBase, size_t runLen);
static int mergeCollapse(struct timsort *ts);
static int mergeForceCollapse(struct timsort *ts);
static int mergeAt(struct timsort *ts, size_t i);
static size_t gallopLeft(void *key, void *base, size_t len,
			 size_t hint, comparator compare, void *udata,
			 size_t width);
static size_t gallopRight(void *key, void *base, size_t len,
			  size_t hint, comparator compare, void *udata,
			  size_t width);
static int mergeLo(struct timsort *ts, void *base1, size_t len1, void *base2,
		   size_t len2);
static int mergeHi(struct timsort *ts, void *base1, size_t len1, void *base2,
		   size_t len2);
static void *ensureCapacity(struct timsort *ts, size_t minCapacity);

/**
 * Creates a TimSort instance to maintain the state of an ongoing sort.
 *
 * @param a the array to be sorted
 * @param nel the length of the array
 * @param c the comparator to determine the order of the sort
 * @param udata data pointer for the comparator
 * @param width the element width
 */
static int timsort_init(struct timsort *ts, void *a, size_t len,
			int (*c) (const void *, const void *, void *),
			void *udata, size_t width)
{
	int stackLen;

	assert(ts);
	assert(a || !len);
	assert(c);
	assert(width);

	ts->minGallop = MIN_GALLOP;
	ts->stackSize = 0;

	ts->a = a;
	ts->a_length = len;
	ts->width = width;
	ts->c = c;
	ts->udata = udata;

	// Allocate temp storage (which may be increased later if necessary)
	ts->tmp_length = (len < 2 * INITIAL_TMP_STORAGE_LENGTH ?
			  len >> 1 : INITIAL_TMP_STORAGE_LENGTH);
	ts->tmp = malloc(ts->tmp_length * width);

	/*
	 * Allocate runs-to-be-merged stack (which cannot be expanded).  The
	 * stack length requirements are described in listsort.txt.  The C
	 * version always uses the same stack length (85), but this was
	 * measured to be too expensive when sorting "mid-sized" arrays (e.g.,
	 * 100 elements) in Java.  Therefore, we use smaller (but sufficiently
	 * large) stack lengths for smaller arrays.  The "magic numbers" in the
	 * computation below must be changed if MIN_MERGE is decreased.  See
	 * the MIN_MERGE declaration above for more information.
	 */

	/* POP:
	 * In listsort.txt, Tim argues that the run lengths form a decreasing
	 * sequence, and each run length is greater than the previous two.
	 * Thus, lower bounds on the minimum runLen numbers on the stack are:
	 *
	 *   [     1
	 *   ,     minRun
	 *   , 1 * minRun + 1 = f[2] * (minRun + 1)  # (also, minRun + 2)
	 *   , 2 * minRun + 2 = f[3] * (minRun + 1)
	 *   , 3 * minRun + 3 = f[4] * (minRun + 1)
	 *   , 5 * minRun + 5 = f[5] * (minRun + 1)
	 *   , ...
	 *   ],
	 *
	 * where f[i] are the Fibonacci numbers: 1, 1, 2, 3, 5, 8, ....
	 *
	 * Moreover, minRun >= MIN_MERGE / 2.  Also, not that the sum of the
	 * run lenghts is less than or equal to the length of the array.
	 *
	 * An array with at most (f[1])        * (minRun + 1) elements can
	 * have stack len at most 2;
	 *  "    "     "  "   "   (f[1] + f[2]) * (minRun + 1)     "     " 
	 *  "    "     "  "   "   3;
	 *  "    "     "  "   "   (f[1] + f[2] + f[3]) * (minRun + 1)     "
	 *  "    "     "  "   "   4.
	 * ...
	 *
	 * Let F[n] = f[1] + ... + f[n].  A stack of length n can accomoduate
	 * arrays of length (MIN_MERGE / 2 + 1) * F[n - 1].
	 *
	 * The value for 'stackLen', below, is determined by the following
	 * table:
	 *
	 *     n    F[n-1]   ((MIN_MERGE / 2  + 1) * F[n-1])
	 *   ------------------------------------------------
	 *     5                     7                    119
	 *    10                    88                   1496
	 *    19                  6764                 114988
	 *    40             165580140             2814862380
	 *    87   1100087778366101930   18701492232223732810    # > 2^64 - 1
	 *
	 * Note that this is slightly more conservative than in the Java
	 * implementation.  The discrepancy might be because the Java
	 * implementation uses a more accurate lower bound.
	 */
	//stackLen = (len < 120 ? 5 : len < 1542 ? 10 : len < 119151 ? 19 : 40);
	stackLen = (len <= 119 ? 5
		    : len <= 1496 ? 10
		    : len <= 114988 ? 19 : len <= 2814862380 ? 40 : 87);

	ts->runBase = malloc(stackLen * sizeof(ts->runBase[0]));
	ts->runLen = malloc(stackLen * sizeof(ts->runLen[0]));

	if (ts->tmp && ts->runBase && ts->runLen) {
		return SUCCESS;
	} else {
		free(ts->tmp);
		free(ts->runBase);
		free(ts->runLen);
		return FAILURE;
	}
}

static void timsort_deinit(struct timsort *ts)
{
	free(ts->tmp);
	free(ts->runBase);
	free(ts->runLen);
}

int timsort(void *a, size_t nel, size_t width,
	    int (*c) (const void *, const void *, void *), void *udata)
{
	assert(a || !nel || !width);
	assert(nel >= 0);
	assert(width >= 0);
	assert(c);

	int err = SUCCESS;

	if (nel < 2 || !width)
		return err;	// Arrays of size 0 and 1 are always sorted

	// If array is small, do a "mini-TimSort" with no merges
	if (nel < MIN_MERGE) {
		size_t initRunLen =
		    countRunAndMakeAscending(a, nel, c, udata, width);
		binarySort(a, nel, initRunLen, c, udata, width);
		return err;
	}

	/**
         * March over the array once, left to right, finding natural runs,
         * extending short natural runs to minRun elements, and merging runs
         * to maintain stack invariant.
         */
	struct timsort ts;
	if ((err = timsort_init(&ts, a, nel, c, udata, width)))
		return err;

	size_t minRun = minRunLength(nel);
	do {
		// Identify next run
		size_t runLen =
		    countRunAndMakeAscending(a, nel, c, udata, width);

		// If run is short, extend to min(minRun, nel)
		if (runLen < minRun) {
			size_t force = nel <= minRun ? nel : minRun;
			binarySort(a, force, runLen, c, udata, width);
			runLen = force;
		}
		// Push run onto pending-run stack, and maybe merge
		pushRun(&ts, a, runLen);
		if ((err = mergeCollapse(&ts)))
			goto out;

		// Advance to find next run
		a += runLen * width;
		nel -= runLen;
	} while (nel != 0);

	// Merge all remaining runs to complete sort
	if ((err = mergeForceCollapse(&ts)))
		goto out;

	assert(ts.stackSize == 1);
out:
	timsort_deinit(&ts);
	return err;
}

/**
 * Sorts the specified portion of the specified array using a binary
 * insertion sort.  This is the best method for sorting small numbers
 * of elements.  It requires O(n log n) compares, but O(n^2) data
 * movement (worst case).
 *
 * If the initial part of the specified range is already sorted,
 * this method can take advantage of it: the method assumes that the
 * elements from index {@code lo}, inclusive, to {@code start},
 * exclusive are already sorted.
 *
 * @param a the array in which a range is to be sorted
 * @param hi the index after the last element in the range to be sorted
 * @param start the index of the first element in the range that is
 *        not already known to be sorted ({@code lo <= start <= hi})
 * @param c comparator to used for the sort
 */
static void binarySort(void *a, size_t hi, size_t start,
		       comparator compare, void *udata, size_t width)
{
	assert(0 <= start && start <= hi);

	char pivot[width];

	if (start == 0)
		start++;

	char *startp = ELEM(a, start);

	for (; start < hi; start++, startp += width) {
		memcpy(pivot, startp, width);

		// Set left (and right) to the index where a[start] (pivot) belongs
		char *left = a;
		size_t right = start;
		assert(left <= right);
		/*
		 * Invariants:
		 *   pivot >= all in [0, left).
		 *   pivot <  all in [right, start).
		 */
		while (0 < right) {
			size_t mid = right >> 1;
			char *pmid = ELEM(left, mid);
			if (compare(pivot, pmid, udata) < 0) {
				right = mid;
			} else {
				left = pmid + width;
				right -= (mid + 1);
			}
		}
		assert(0 == right);

		/*
		 * The invariants still hold: pivot >= all in [lo, left) and
		 * pivot < all in [left, start), so pivot belongs at left.  Note
		 * that if there are elements equal to pivot, left points to the
		 * first slot after them -- that's why this sort is stable.
		 * Slide elements over to make room to make room for pivot.
		 */
		size_t n = startp - left; // The number of elements to move
		memmove(left + width, left, n);


		// a[left] = pivot;
		memcpy(left, pivot, width);
	}
}

/**
 * Returns the length of the run beginning at the specified position in
 * the specified array and reverses the run if it is descending (ensuring
 * that the run will always be ascending when the method returns).
 *
 * A run is the longest ascending sequence with:
 *
 *    a[0] <= a[1] <= a[2] <= ...
 *
 * or the longest descending sequence with:
 *
 *    a[0] >  a[1] >  a[2] >  ...
 *
 * For its intended use in a stable mergesort, the strictness of the
 * definition of "descending" is needed so that the call can safely
 * reverse a descending sequence without violating stability.
 *
 * @param a the array in which a run is to be counted and possibly reversed
 * @param hi index after the last element that may be contained in the run.
 *        It is required that {@code 0 < hi}.
 * @param compare the comparator to used for the sort
 * @return  the length of the run beginning at the specified position in
 *          the specified array
 */
static size_t countRunAndMakeAscending(void *a, size_t hi,
				       comparator compare, void *udata,
				       size_t width)
{
	assert(0 < hi);
	size_t runHi = 1;
	if (runHi == hi)
		return 1;

	char *cur = ELEM(a, runHi++);
	char *next = cur + width;

	// Find end of run, and reverse range if descending
	if (compare(cur, a, udata) < 0) { // Descending
		while (runHi < hi && compare(next, cur, udata) < 0) {
			runHi++;
			cur = next;
			next += width;
		}
		reverseRange(a, 0, runHi, width);
	} else {		// Ascending
		while (runHi < hi && compare(next, cur, udata) >= 0) {
			runHi++;
			cur = next;
			next += width;
		}
	}

	return runHi;
}

/**
 * Reverse the specified range of the specified array.
 *
 * @param a the array in which a range is to be reversed
 * @param lo the index of the first element in the range to be reversed
 * @param hi the index after the last element in the range to be reversed
 */
static void reverseRange(void *a, size_t lo, size_t hi, size_t width)
{
	char t[width];

	while (lo + 1 < hi) {
		memcpy(t, ELEM(a, lo), width);
		memcpy(ELEM(a, lo), ELEM(a, hi - 1), width);
		memcpy(ELEM(a, hi - 1), t, width);
		lo++;
		hi--;
	}
}

/**
 * Returns the minimum acceptable run length for an array of the specified
 * length. Natural runs shorter than this will be extended with
 * {@link #binarySort}.
 *
 * Roughly speaking, the computation is:
 *
 *  If n < MIN_MERGE, return n (it's too small to bother with fancy stuff).
 *  Else if n is an exact power of 2, return MIN_MERGE/2.
 *  Else return an int k, MIN_MERGE/2 <= k <= MIN_MERGE, such that n/k
 *   is close to, but strictly less than, an exact power of 2.
 *
 * For the rationale, see listsort.txt.
 *
 * @param n the length of the array to be sorted
 * @return the length of the minimum run to be merged
 */
static size_t minRunLength(size_t n)
{
	assert(n >= 0);
	size_t r = 0;		// Becomes 1 if any 1 bits are shifted off
	while (n >= MIN_MERGE) {
		r |= (n & 1);
		n >>= 1;
	}
	return n + r;
}

/**
 * Pushes the specified run onto the pending-run stack.
 *
 * @param runBase index of the first element in the run
 * @param runLen  the number of elements in the run
 */
static void pushRun(struct timsort *ts, void *runBase, size_t runLen)
{
	ts->runBase[ts->stackSize] = runBase;
	ts->runLen[ts->stackSize] = runLen;
	ts->stackSize++;
}

/**
 * Examines the stack of runs waiting to be merged and merges adjacent runs
 * until the stack invariants are reestablished:
 *
 *     1. runLen[i - 3] > runLen[i - 2] + runLen[i - 1]
 *     2. runLen[i - 2] > runLen[i - 1]
 *
 * This method is called each time a new run is pushed onto the stack,
 * so the invariants are guaranteed to hold for i < stackSize upon
 * entry to the method.
 */
static int mergeCollapse(struct timsort *ts)
{
	int err = SUCCESS;

	while (ts->stackSize > 1) {
		size_t n = ts->stackSize - 2;
		if (n > 0
		    && ts->runLen[n - 1] <= ts->runLen[n] + ts->runLen[n + 1]) {
			if (ts->runLen[n - 1] < ts->runLen[n + 1])
				n--;
			err = mergeAt(ts, n);
			if (err)
				break;
		} else if (ts->runLen[n] <= ts->runLen[n + 1]) {
			err = mergeAt(ts, n);
			if (err)
				break;
		} else {
			break;	// Invariant is established
		}
	}

	return err;
}

/**
 * Merges all runs on the stack until only one remains.  This method is
 * called once, to complete the sort.
 */
static int mergeForceCollapse(struct timsort *ts)
{
	int err = SUCCESS;

	while (ts->stackSize > 1) {
		size_t n = ts->stackSize - 2;
		if (n > 0 && ts->runLen[n - 1] < ts->runLen[n + 1])
			n--;
		err = mergeAt(ts, n);
		if (err)
			break;
	}

	return err;
}

/**
 * Merges the two runs at stack indices i and i+1.  Run i must be
 * the penultimate or antepenultimate run on the stack.  In other words,
 * i must be equal to stackSize-2 or stackSize-3.
 *
 * @param i stack index of the first of the two runs to merge
 */
static int mergeAt(struct timsort *ts, size_t i)
{
	assert(ts->stackSize >= 2);
	assert(i >= 0);
	assert(i == ts->stackSize - 2 || i == ts->stackSize - 3);

	size_t width = ts->width;

	void *base1 = ts->runBase[i];
	size_t len1 = ts->runLen[i];
	void *base2 = ts->runBase[i + 1];
	size_t len2 = ts->runLen[i + 1];
	assert(len1 > 0 && len2 > 0);
	assert(base1 + len1 * width == base2);

	/*
	 * Record the length of the combined runs; if i is the 3rd-last
	 * run now, also slide over the last run (which isn't involved
	 * in this merge).  The current run (i+1) goes away in any case.
	 */
	ts->runLen[i] = len1 + len2;
	if (i == ts->stackSize - 3) {
		ts->runBase[i + 1] = ts->runBase[i + 2];
		ts->runLen[i + 1] = ts->runLen[i + 2];
	}
	ts->stackSize--;

	/*
	 * Find where the first element of run2 goes in run1. Prior elements
	 * in run1 can be ignored (because they're already in place).
	 */
	size_t k = gallopRight(base2, base1, len1, 0, ts->c, ts->udata,
			       width);
	assert(k >= 0);
	base1 += k * width;
	len1 -= k;
	if (len1 == 0)
		return SUCCESS;

	/*
	 * Find where the last element of run1 goes in run2. Subsequent elements
	 * in run2 can be ignored (because they're already in place).
	 */
	len2 =
	    gallopLeft(ELEM(base1, len1 - 1), base2, len2, len2 - 1,
		       ts->c, ts->udata, width);
	assert(len2 >= 0);
	if (len2 == 0)
		return SUCCESS;

	// Merge remaining runs, using tmp array with min(len1, len2) elements
	if (len1 <= len2)
		return mergeLo(ts, base1, len1, base2, len2);
	else
		return mergeHi(ts, base1, len1, base2, len2);
}

/**
 * Locates the position at which to insert the specified key into the
 * specified sorted range; if the range contains an element equal to key,
 * returns the index of the leftmost equal element.
 *
 * @param key the key whose insertion point to search for
 * @param base the array in which to search
 * @param len the length of the range; must be > 0
 * @param hint the index at which to begin the search, 0 <= hint < n.
 *     The closer hint is to the result, the faster this method will run.
 * @param c the comparator used to order the range, and to search
 * @return the int k,  0 <= k <= n such that a[b + k - 1] < key <= a[b + k],
 *    pretending that a[b - 1] is minus infinity and a[b + n] is infinity.
 *    In other words, key belongs at index b + k; or in other words,
 *    the first k elements of a should precede key, and the last n - k
 *    should follow it.
 */
static size_t gallopLeft(void *key, void *base, size_t len,
			 size_t hint, comparator compare, void *udata,
			 size_t width)
{
	assert(len > 0 && hint >= 0 && hint < len);
	char *hintp = ELEM(base, hint);
	size_t lastOfs = 0;
	size_t ofs = 1;

	if (compare(key, hintp, udata) > 0) {
		// Gallop right until a[hint+lastOfs] < key <= a[hint+ofs]
		size_t maxOfs = len - hint;
		while (ofs < maxOfs
		       && compare(key, ELEM(hintp, ofs), udata) > 0) {
			lastOfs = ofs;
			ofs = (ofs << 1) + 1;	// eventually this becomes SIZE_MAX
		}
		if (ofs > maxOfs)
			ofs = maxOfs;

		// Make offsets relative to base
		lastOfs += hint + 1;	// POP: we add 1 here so lastOfs stays non-negative
		ofs += hint;
	} else {		// key <= a[hint]
		// Gallop left until a[hint-ofs] < key <= a[hint-lastOfs]
		const size_t maxOfs = hint + 1;
		while (ofs < maxOfs
		       && compare(key, ELEM(hintp, -ofs), udata) <= 0) {
			lastOfs = ofs;
			ofs = (ofs << 1) + 1;	// no need to check for overflow
		}
		if (ofs > maxOfs)
			ofs = maxOfs;

		// Make offsets relative to base
		size_t tmp = lastOfs;
		lastOfs = hint + 1 - ofs;	// POP: we add 1 here so lastOfs stays non-negative
		ofs = hint - tmp;
	}
	assert(0 <= lastOfs && lastOfs <= ofs && ofs <= len);

	/*
	 * Now a[lastOfs-1] < key <= a[ofs], so key belongs somewhere
	 * to the right of lastOfs but no farther right than ofs.  Do a binary
	 * search, with invariant a[lastOfs - 1] < key <= a[ofs].
	 */
	// lastOfs++; POP: we added 1 above to keep lastOfs non-negative
	while (lastOfs < ofs) {
		//size_t m = lastOfs + ((ofs - lastOfs) >> 1);
		// http://stackoverflow.com/questions/4844165/safe-integer-middle-value-formula
		size_t m = (lastOfs & ofs) + ((lastOfs ^ ofs) >> 1);

		if (compare(key, ELEM(base, m), udata) > 0)
			lastOfs = m + 1;	// a[m] < key
		else
			ofs = m;	// key <= a[m]
	}
	assert(lastOfs == ofs);	// so a[ofs - 1] < key <= a[ofs]
	return ofs;
}

/**
 * Like gallopLeft, except that if the range contains an element equal to
 * key, gallopRight returns the index after the rightmost equal element.
 *
 * @param key the key whose insertion point to search for
 * @param base the array in which to search
 * @param len the length of the range; must be > 0
 * @param hint the index at which to begin the search, 0 <= hint < n.
 *     The closer hint is to the result, the faster this method will run.
 * @param c the comparator used to order the range, and to search
 * @return the int k,  0 <= k <= n such that a[b + k - 1] <= key < a[b + k]
 */
static size_t gallopRight(void *key, void *base, size_t len,
			  size_t hint, comparator compare, void *udata,
			  size_t width)
{
	assert(len > 0 && hint >= 0 && hint < len);

	char *hintp = ELEM(base, hint);
	size_t ofs = 1;
	size_t lastOfs = 0;

	if (compare(key, hintp, udata) < 0) {
		// Gallop left until a[hint - ofs] <= key < a[hint - lastOfs]
		size_t maxOfs = hint + 1;
		while (ofs < maxOfs
		       && compare(key, ELEM(hintp, -ofs), udata) < 0) {
			lastOfs = ofs;
			ofs = (ofs << 1) + 1;	// no need to check for overflow
		}
		if (ofs > maxOfs)
			ofs = maxOfs;

		// Make offsets relative to base
		size_t tmp = lastOfs;
		lastOfs = hint + 1 - ofs;
		ofs = hint - tmp;
	} else {		// a[hint] <= key
		// Gallop right until a[hint + lastOfs] <= key < a[hint + ofs]
		size_t maxOfs = len - hint;
		while (ofs < maxOfs
		       && compare(key, ELEM(hintp, ofs), udata) >= 0) {
			lastOfs = ofs;
			ofs = (ofs << 1) + 1;	// no need to check for overflow
		}
		if (ofs > maxOfs)
			ofs = maxOfs;

		// Make offsets relative to base
		lastOfs += hint + 1;
		ofs += hint;
	}
	assert(0 <= lastOfs && lastOfs <= ofs && ofs <= len);

	/*
	 * Now a[lastOfs - 1] <= key < a[ofs], so key belongs somewhere to
	 * the right of lastOfs but no farther right than ofs.  Do a binary
	 * search, with invariant a[lastOfs - 1] <= key < a[ofs].
	 */
	while (lastOfs < ofs) {
		// size_t m = lastOfs + ((ofs - lastOfs) >> 1);
		size_t m = (lastOfs & ofs) + ((lastOfs ^ ofs) >> 1);

		if (compare(key, ELEM(base, m), udata) < 0)
			ofs = m;	// key < a[m]
		else
			lastOfs = m + 1;	// a[m] <= key
	}
	assert(lastOfs == ofs);	// so a[ofs - 1] <= key < a[ofs]
	return ofs;
}

/**
 * Merges two adjacent runs in place, in a stable fashion.  The first
 * element of the first run must be greater than the first element of the
 * second run (a[base1] > a[base2]), and the last element of the first run
 * (a[base1 + len1-1]) must be greater than all elements of the second run.
 *
 * For performance, this method should be called only when len1 <= len2;
 * its twin, mergeHi should be called if len1 >= len2.  (Either method
 * may be called if len1 == len2.)
 *
 * @param base1 first element in first run to be merged
 * @param len1  length of first run to be merged (must be > 0)
 * @param base2 first element in second run to be merged
 *        (must be aBase + aLen)
 * @param len2  length of second run to be merged (must be > 0)
 */
static int mergeLo(struct timsort *ts, void *base1, size_t len1, void *base2,
		   size_t len2)
{
	size_t width = ts->width;

	assert(len1 > 0 && len2 > 0 && base1 + len1 * width == base2);

	// Copy first run into temp array
	void *tmp = ensureCapacity(ts, len1);
	if (!tmp)
		return FAILURE;

	// System.arraycopy(a, base1, tmp, 0, len1);
	memcpy(tmp, base1, len1 * width);

	char *cursor1 = tmp;	// Indexes into tmp array
	char *cursor2 = base2;	// Indexes int a
	char *dest = base1;	// Indexes int a

	// Move first element of second run and deal with degenerate cases
	// a[dest++] = a[cursor2++];
	memcpy(dest, cursor2, width);
	dest += width;
	cursor2 += width;

	if (--len2 == 0) {
		memcpy(dest, cursor1, len1 * width);
		return SUCCESS;
	}
	if (len1 == 1) {
		memcpy(dest, cursor2, len2 * width);

		// a[dest + len2] = tmp[cursor1]; // Last elt of run 1 to end of merge
		memcpy(dest + len2 * width, cursor1, width);
		return SUCCESS;
	}

	comparator compare = ts->c;	// Use local variable for performance
	void *udata = ts->udata;
	size_t minGallop = ts->minGallop;	//  "    "       "     "      "

	while (1) {
		size_t count1 = 0;	// Number of times in a row that first run won
		size_t count2 = 0;	// Number of times in a row that second run won

		/*
		 * Do the straightforward thing until (if ever) one run starts
		 * winning consistently.
		 */
		do {
			assert(len1 > 1 && len2 > 0);
			if (compare(cursor2, cursor1, udata) < 0) {
				memcpy(dest, cursor2, width);
				dest += width;
				cursor2 += width;
				count2++;
				count1 = 0;
				if (--len2 == 0)
					goto outer;
				if (count2 >= minGallop)
					break;
			} else {
				memcpy(dest, cursor1, width);
				dest += width;
				cursor1 += width;
				count1++;
				count2 = 0;
				if (--len1 == 1)
					goto outer;
				if (count1 >= minGallop)
					break;
			}
		} while (1);	// (count1 | count2) < minGallop);

		/*
		 * One run is winning so consistently that galloping may be a
		 * huge win. So try that, and continue galloping until (if ever)
		 * neither run appears to be winning consistently anymore.
		 */
		do {
			assert(len1 > 1 && len2 > 0);
			count1 =
			    gallopRight(cursor2, cursor1, len1, 0,
					compare, udata, width);
			if (count1 != 0) {
				memcpy(dest, cursor1, count1 * width);
				dest += count1 * width;
				cursor1 += count1 * width;
				len1 -= count1;
				if (len1 <= 1)	// len1 == 1 || len1 == 0
					goto outer;
			}
			memcpy(dest, cursor2, width);
			dest += width;
			cursor2 += width;
			if (--len2 == 0)
				goto outer;

			count2 =
			    gallopLeft(cursor1, cursor2, len2, 0,
				       compare, udata, width);
			if (count2 != 0) {
				memcpy(dest, cursor2, count2 * width);
				dest += count2 * width;
				cursor2 += count2 * width;
				len2 -= count2;
				if (len2 == 0)
					goto outer;
			}
			memcpy(dest, cursor1, width);
			dest += width;
			cursor1 += width;
			if (--len1 == 1)
				goto outer;
			if (minGallop > 0)
				minGallop--;
		} while (count1 >= MIN_GALLOP || count2 >= MIN_GALLOP);
		minGallop += 2;	// Penalize for leaving gallop mode
	}			// End of "outer" loop
outer:
	ts->minGallop = minGallop < 1 ? 1 : minGallop;	// Write back to field

	if (len1 == 1) {
		assert(len2 > 0);
		memcpy(dest, cursor2, len2 * width);
		memcpy(dest + len2 * width, cursor1, width);	//  Last elt of run 1 to end of merge

	} else if (len1 == 0) {
		errno = EINVAL;	// Comparison method violates its general contract
		return FAILURE;
	} else {
		assert(len2 == 0);
		assert(len1 > 1);
		memcpy(dest, cursor1, len1 * width);
	}
	return SUCCESS;
}

/**
 * Like mergeLo, except that this method should be called only if
 * len1 >= len2; mergeLo should be called if len1 <= len2.  (Either method
 * may be called if len1 == len2.)
 *
 * @param base1 first element in first run to be merged
 * @param len1  length of first run to be merged (must be > 0)
 * @param base2 first element in second run to be merged
 *        (must be aBase + aLen)
 * @param len2  length of second run to be merged (must be > 0)
 */
static int mergeHi(struct timsort *ts, void *base1, size_t len1, void *base2,
		   size_t len2)
{
	size_t width = ts->width;

	assert(len1 > 0 && len2 > 0 && base1 + len1 * width == base2);

	// Copy second run into temp array
	void *tmp = ensureCapacity(ts, len2);
	if (!tmp)
		return FAILURE;

	memcpy(tmp, base2, len2 * width);

	char *cursor1 = ELEM(base1, len1 - 1);	// Indexes into a
	char *cursor2 = ELEM(tmp, len2 - 1);	// Indexes into tmp array
	char *dest = ELEM(base2, len2 - 1);	// Indexes into a

	// Move last element of first run and deal with degenerate cases
	// a[dest--] = a[cursor1--];
	memcpy(dest, cursor1, width);
	dest -= width;
	cursor1 -= width;
	if (--len1 == 0) {
		memcpy(dest - (len2 - 1) * width, tmp, len2 * width);
		return SUCCESS;
	}
	if (len2 == 1) {
		dest -= len1 * width;
		cursor1 -= len1 * width;
		memcpy(dest + width, cursor1 + width, len1 * width);
		// a[dest] = tmp[cursor2];
		memcpy(dest, cursor2, width);
		return SUCCESS;
	}

	comparator compare = ts->c;	// Use local variable for performance
	void *udata = ts->udata;
	size_t minGallop = ts->minGallop;	//  "    "       "     "      "

	while (1) {
		size_t count1 = 0;	// Number of times in a row that first run won
		size_t count2 = 0;	// Number of times in a row that second run won

		/*
		 * Do the straightforward thing until (if ever) one run
		 * appears to win consistently.
		 */
		do {
			assert(len1 > 0 && len2 > 1);
			if (compare(cursor2, cursor1, udata) < 0) {
				memcpy(dest, cursor1, width);
				dest -= width;
				cursor1 -= width;
				count1++;
				count2 = 0;
				if (--len1 == 0)
					goto outer;
			} else {
				memcpy(dest, cursor2, width);
				dest -= width;
				cursor2 -= width;
				count2++;
				count1 = 0;
				if (--len2 == 1)
					goto outer;
			}
		} while ((count1 | count2) < minGallop);

		/*
		 * One run is winning so consistently that galloping may be a
		 * huge win. So try that, and continue galloping until (if ever)
		 * neither run appears to be winning consistently anymore.
		 */
		do {
			assert(len1 > 0 && len2 > 1);
			count1 =
			    len1 - gallopRight(cursor2, base1,
					       len1, len1 - 1, compare, udata,
					       width);
			if (count1 != 0) {
				dest -= count1 * width;
				cursor1 -= count1 * width;
				len1 -= count1;
				memcpy(dest + width, cursor1 + width,
				       count1 * width);
				if (len1 == 0)
					goto outer;
			}
			memcpy(dest, cursor2, width);
			dest -= width;
			cursor2 -= width;
			if (--len2 == 1)
				goto outer;

			count2 =
			    len2 - gallopLeft(cursor1, tmp, len2,
					      len2 - 1, compare, udata, width);
			if (count2 != 0) {
				dest -= count2 * width;
				cursor2 -= count2 * width;
				len2 -= count2;
				memcpy(dest + width,
				       cursor2 + width, count2 * width);
				if (len2 <= 1)	// len2 == 1 || len2 == 0
					goto outer;
			}
			memcpy(dest, cursor1, width);
			dest -= width;
			cursor1 -= width;
			if (--len1 == 0)
				goto outer;
			if (minGallop > 0)
				minGallop--;
		} while (count1 >= MIN_GALLOP || count2 >= MIN_GALLOP);
		minGallop += 2;	// Penalize for leaving gallop mode
	}			// End of "outer" loop
outer:
	ts->minGallop = minGallop < 1 ? 1 : minGallop;	// Write back to field

	if (len2 == 1) {
		assert(len1 > 0);
		dest -= len1 * width;
		cursor1 -= len1 * width;
		memcpy(dest + width, cursor1 + width, len1 * width);
		// a[dest] = tmp[cursor2];  // Move first elt of run2 to front of merge
		memcpy(dest, cursor2, width);
	} else if (len2 == 0) {
		errno = EINVAL;	// Comparison method violates its general contract
		return FAILURE;
	} else {
		assert(len1 == 0);
		assert(len2 > 0);
		memcpy(dest - (len2 - 1) * width, tmp, len2 * width);
	}

	return SUCCESS;
}

/**
 * Ensures that the external array tmp has at least the specified
 * number of elements, increasing its size if necessary.  The size
 * increases exponentially to ensure amortized linear time complexity.
 *
 * @param minCapacity the minimum required capacity of the tmp array
 * @return tmp, whether or not it grew
 */
static void *ensureCapacity(struct timsort *ts, size_t minCapacity)
{
	void *tmp = ts->tmp;

	if (ts->tmp_length < minCapacity) {
		// Compute smallest power of 2 > minCapacity
		size_t newSize = minCapacity;
		newSize |= newSize >> 1;
		newSize |= newSize >> 2;
		newSize |= newSize >> 4;
		newSize |= newSize >> 8;
		newSize |= newSize >> 16;
		if (sizeof(newSize) > 4)
			newSize |= newSize >> 32;

		newSize++;
		newSize = MIN(newSize, ts->a_length >> 1);
		if (newSize == 0) {	// (overflow) Not bloody likely!
			newSize = minCapacity;
		}

		tmp = realloc(ts->tmp, newSize * ts->width);
		if (tmp) {
			ts->tmp = tmp;
			ts->tmp_length = newSize;
		}
	}

	return tmp;
}
