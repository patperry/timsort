/* Modified version of Christopher Swenson's 'stresstest.c' from
 * https://github.com/swenson/sort/blob/master/stresstest.c
 *
 * Copyright (c) 2011 Patrick 0. Perry
 * Copyright (c) 2010 Christopher Swenson
 *
 * Permission is hereby granted, free of charge, to any person
 * obtaining a copy of this software and associated documentation
 * files (the "Software"), to deal in the Software without
 * restriction, including without limitation the rights to use, copy,
 * modify, merge, publish, distribute, sublicense, and/or sell copies
 * of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be
 * included in all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
 * EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
 * MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
 * NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS
 * BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN
 * ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
 * CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
 * SOFTWARE.
 */

#include <errno.h>
#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#include <sys/time.h>
#include "timsort.h"

/* Used to control the stress test */
#define SEED 123
#define MAXSIZE 25600
#define TESTS 10000
#define TYPE int

/* helper functions */
void verify(TYPE *dst, const size_t size)
{
  size_t i;
  for (i = 1; i < size; i++)
  {
    if (dst[i - 1] > dst[i])
    {
	    printf("Verify failed! at %zd\n", i);
	    //for (i = i - 2; i < size; i++)
	    //  printf(" %lld", dst[i]);
	    //printf("\n");
	    break;
    }
  }
}

static void fill(TYPE *dst, const size_t size)
{
  size_t i;
  for (i = 0; i < size; i++)
  {
    dst[i] = lrand48();
  }
}

/* used for stdlib */
static inline int compare(const void *a, const void *b)
{
  const TYPE da = *((const TYPE *) a);
  const TYPE db = *((const TYPE *) b);
  return (da < db) ? -1 : (da == db) ? 0 : 1;
}

static inline int compare_udata(const void *a, const void *b, void *udata)
{
  const TYPE da = *((const TYPE *) a);
  const TYPE db = *((const TYPE *) b);
  return (da < db) ? -1 : (da == db) ? 0 : 1;
}


void run_tests(void)
{
	int err;
	int test;
	TYPE *dst;
	size_t size;
	
	printf("Running tests\n");
	srand48(SEED);

#if 1
	printf("timsort\n");
	for (test = 0; test < TESTS; test++)
	{
		size = (lrand48() % (MAXSIZE + 1));
		dst = malloc(size * sizeof(dst[0]));
		if (!dst && size) {
			perror("malloc failed");
			exit(EXIT_FAILURE);
		}

		fill(dst, size);
		err = timsort(dst, size, sizeof(dst[0]), compare_udata, NULL);
		if (err) {
			perror("timsort failed");
			exit(EXIT_FAILURE);
		}
		verify(dst, size);
		
		free(dst);
	} 
#endif
#if 0
	printf("mergesort\n");
	for (test = 0; test < TESTS; test++)
	{
		size = (lrand48() % (MAXSIZE + 1));
		dst = malloc(size * sizeof(dst[0]));
		if (!dst && size) {
			perror("malloc failed");
			exit(EXIT_FAILURE);
		}

		fill(dst, size);
		err = mergesort(dst, size, sizeof(dst[0]), compare);
		if (err) {
			perror("mergesort failed");
			exit(EXIT_FAILURE);
		}
		verify(dst, size);
		
		free(dst);
	} 
#endif
}

int main(void)
{
	run_tests();
	return EXIT_SUCCESS;
}
