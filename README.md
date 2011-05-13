This is a fairly straightforward C99 port of the Java/Android
implementation of [Timsort](http://en.wikipedia.org/wiki/Timsort), which
itself is a port of Tim Peters's list sort for Python.  Most of the
comments are from the Android implementation, except those annotated
by the initials POP.

The prototype for the sorting function is

    int timsort(void *base, size_t nel, size_t width,
                int (*compar) (const void *, const void *, void *), void *udata);

This resembles the standard library `qsort` function, except that the
comparator takes a third `udata` parameter, which is supplied by the
client.  The function returns `0` on success and `-1` on failure.  Failure
only happens when the routine can't allocate the necessary temporary array or
if the comparator is invalid.

The C version uses a few C99 variable length arrays of size `width`; these
could easily be replaced with calls to `alloca`.  The other C99 features
used are mixed code and declarations, and the `stdint.h` header
(for `SIZE_MAX`).  It would be fairly easy to port the code to C90.

The source for the (Apache 2.0 Licensed) Java version is included in
[the JSR-166 proposal](http://gee.cs.oswego.edu/cgi-bin/viewcvs.cgi/jsr166/src/main/java/util/TimSort.java?view=co).

This version would not be possiple without all the hard work on the Java
version.  Kudos to google for open-sourcing their code.  I've applied the
same license to the C version, and kept the "Android Open Source Project"
copyright on the code.  An even bigger "thank you" goes to Tim Peters,
for devising and documenting the algorithm in the first place.


Differences from the Java version
=================================

C doesn't have exceptions, so I use `errno` and return codes instead.
I switched from 'int' to 'size_t' as the index type.  This required
some extra care in checking for overflow and ensuring the indices
are always non-negative.  Moreover, the types have different sizes
on 64-bit platforms.  Finally, I fixed a potential overflow bug in the
Java version of `binarySort`.


Use return codes instead of exceptions
--------------------------------------

In the C implementation, if `malloc` or `realloc` fails to allocate the
necessary temporary array, the sorting routine returns `-1`.
Likewise, if `mergeLo` or `mergeHi` discovers that the comparison
method violates its contract, then it sets `errno` to `EINVAL` and
returns the sorting routine returns `-1`.



Switch from signed to unsigned
------------------------------

The following changes are related to signed/unsigned differences in
the index types.

-   In `gallopLeft` and `gallopRight`, I replaced

        ofs = (ofs << 1) + 1;
        if (ofs <= 0)   // int overflow
            ofs = maxOfs;

    with

        if ((ofs << 1) + 1 > ofs) {
            ofs = (ofs << 1) + 1;
        } else {  // overflow
            ofs = maxOfs;
        }

-   In the Java version of `gallopLeft`, the `lastOfs` variable is
    allowed to become `-1`.  To prevent this, in the `else` branch
    I replaced

        lastOfs = hint - ofs;

    with

        lastOfs = hint + 1 - ofs;

    for symmetry, in the `if` branch I replaced `lastOfs += hint` with
    `lastOfs += hint + 1`.  Finally, I replaced
    
        assert(-1 <= lastOfs && lastOfs < ofs && ofs <= len);

    with

        assert(0 <= lastOfs && lastOfs <= ofs && ofs <= len);

    and I commented out the statement `lastOfs++;` which happens after
    the conditional.  I made similar changes to `gallopRight`.

-   In `mergeLo`, I replaced

        minGallop--;

    with

        if (minGallop > 0)
            minGallop--;

    Then, I removed following lines, which appear after the loop:

        if (minGallop < 0)
            minGallop = 0;

    I made a similar change for `mergeHi`.

-   In `ensureCapacity`, I replaced

        if (newSize < 0) // Not bloody likely!
            newSize = minCapacity;
        else
            newSize = MIN(newSize, a.length >> 1);

    with

        if (newSize < SIZE_MAX) {
            newSize++;
            newSize = MIN(newSize, ts->a_length >> 1);
        } else {	// Not bloody likely!
            newSize = minCapacity;
        }


        if (sizeof(newSize) > 4)
            newSize |= newSize >> 32;

-   I re-wrote `reverseRange` to ensure that `hi` never becomes negative.

Switch from 32-bit to (potentially) 64-bit
------------------------------------------

The rest of the changes allow for `size_t` to be up to 64-bits long:

-   In the TimSort constructor (`timsort_init`), I replaced

        stackLen = (len < 120 ? 5 : len < 1542 ? 10 : len < 119151 ? 19 : 40);

    with

        stackLen = (len <= 119 ? 5
		            : len <= 1496 ? 10
        		    : len <= 114988 ? 19 : len <= 2814862380 ? 40 : 87);

     Note that the bounds on `len` are slightly different.  I explain the
     justification for these values in a comment above the assignment.

-    In `ensureCapacity`, I added

        if (sizeof(newSize) > 4)
            newSize |= newSize >> 32;


Guard agains overflow in midpoint computation
---------------------------------------------

The Java implentation of `binarySort` computes the midpoint of `left` and
`right` in an unsafe manner.  To fix this, I replaced

    mid = (left + right) >> 1;

with

    mid = (left & right) + ((left ^ right) >> 1)

This slightly exotic formula is explain on [stackoverflow.com](http://stackoverflow.com/questions/4844165/safe-integer-middle-value-formula).
