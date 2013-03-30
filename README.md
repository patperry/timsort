This is a fork of [Pat Perry's timsort](https://github.com/patperry/timsort)
C implementation. Please see the end of this README for the changes in
this fork. - Ashok P. Nadkarni

This is a fairly straightforward C99 port of the Java/Android
implementation of [Timsort](http://en.wikipedia.org/wiki/Timsort), which
itself is a port of Tim Peters's list sort for Python.  Most of the
comments are from the earlier two implementations, except those annotated
by the initials POP.

The prototype for the sorting function is

    int timsort(void *base, size_t nel, size_t width,
                int (*compar) (const void *, const void *));

This resembles the standard library `qsort` function.  The function
returns `0` on success and `-1` on failure.  Failure only happens when
the routine can't allocate the necessary temporary array or if the
comparator is invalid.

The C version uses a few C99 variable length arrays of size `width`; these
could easily be replaced with calls to `alloca`.  The other utilized C99 features
are mixed code and declarations, and `//` comments.  It would be fairly easy to
port the code to C90.

The source code for the (Apache 2.0 Licensed) Java version is included in
[the JSR-166 proposal](http://gee.cs.oswego.edu/cgi-bin/viewcvs.cgi/jsr166/src/main/java/util/TimSort.java?view=co).

This version would not be possiple without all the hard work on the Java
version.  Kudos to google for open-sourcing their code.  This implementation
has same license, and maintains the "Android Open Source Project"
copyright on the code.  An even bigger "thank you" goes to Tim Peters,
for devising and documenting the algorithm in the first place.


Differences from the Java version
=================================

C doesn't have exceptions, so we use `errno` and return codes instead.  Another
difference is that C has pointers, so there is no need to pass around a `lo`
parameter to specify a range of values in an array.
One major change is that we use 'size_t' instead of 'int' as the index type; this
required some extra care in checking for overflow and ensuring that
the values are always non-negative.  Moreover, some modifications needed to
be made to allow for differences on 64-bit architectures.  These changes
are explained in more detail below.


Use return codes instead of exceptions
--------------------------------------

In the C implementation, if `malloc` or `realloc` fails to allocate the
necessary temporary array, the sorting routine returns `-1`.
Likewise, if `mergeLo` or `mergeHi` discovers that the comparison
method violates its contract, then it sets `errno` to `EINVAL` and
the sorting routine returns `-1`.


Use pointers instead of arrays with offsets
-------------------------------------------

C has pointers, so there is no need to pass around "lo" parameters.  Instead,
we store the poniter to the base of the array range.


Switch from `int` to `size_t`
-----------------------------

The code takes special care to ensure that integer values never become
negative; in particular:

-   In the Java version of `gallopLeft`, the `lastOfs` variable is
    allowed to become `-1`.  To prevent this, in the `else` branch
    we replace

        lastOfs = hint - ofs;

    with

        lastOfs = hint + 1 - ofs;

    for symmetry, in the `if` branch we replace `lastOfs += hint` with
    `lastOfs += hint + 1`.  Finally, we replace
    
        assert(-1 <= lastOfs && lastOfs < ofs && ofs <= len);

    with

        assert(0 <= lastOfs && lastOfs <= ofs && ofs <= len);

    and remove the statement `lastOfs++;` which happens after
    the conditional.  Similar changes appear in `gallopRight`.

-   In `mergeLo`, we replace

        minGallop--;

    with

        if (minGallop > 0)
            minGallop--;

    Then, we remove following lines, which appear after the loop:

        if (minGallop < 0)
            minGallop = 0;

    Similar changes appear in `mergeHi`.

The rest of the changes allow for `size_t` to be up to 64-bits long:

-   In the TimSort constructor (`timsort_init`), the line

        stackLen = (len < 120 ? 5 : len < 1542 ? 10 : len < 119151 ? 19 : 40);

    gets replaced with with

	    stackLen = (len < 359 ? 5
			        : len < 4220 ? 10
			        : len < 76210 ? 16 : len < 4885703256 ? 39 : 85);

    Note that the bounds on `len` are slightly different.  The
    justification for these values is given in a comment above the assignment.

-   In `ensureCapacity`, we add an additional operation:

        if (sizeof(newSize) > 4)
            newSize |= newSize >> 32;


Related projects
================

Christopher Swenson has a macro-based C implementation of timsort at
[https://github.com/swenson/sort/](https://github.com/swenson/sort/).


Performance
===========

In a crude benchmark, sorting small, medium, and large arrays of
uniformly chosen 64-bit integers, performance was comparable to the
stdlib `qsort` implementation; Swenson's macro-based timsort
implementation was about 1.4 times faster than both.  Swenson's
implementation has the edge here because it avoids the overhead
of a function call when comparing two elements.

Changes in this fork
===================

This fork has two primary differences from Pat Perry's original implementation
but should be backward compatible.

Visual C++ / C90 compatibility
------------------------------

The source has been changed so that it can be compiled with Visual C++.
Most changes are those described above in the original README. However,
instead of using alloca, a MAX_WIDTH #define controls maximum size
of elements allowed.

timsort_r
-----------

A variation of the timsort() function - timsort_r() - has been defined
which can pass an additional argument to the comparison function
purely for the calling application's own use. This is similar to the
BSD (*not* GNU) qsort_r variation of the standard qsort function. 

The prototype for this sorting function is

    int timsort_r(void *base, size_t nel, size_t width,
                int (*compar) (void *context, const void *, const void *), 
		void *context);

The additional context parameter is passed to the comparison callback
as the first argument. To build this variation, pass /DUSE_CMP_ARG 
to the compiler.

Functions timsort and timsort_r may be simultaneously included in a program.
Just build two object files from timsort.c, one with /DUSE_CMP_ARG and
one without.
