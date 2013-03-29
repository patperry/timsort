/* Demo of failure on Linux/gcc 4.4 due to use of memcpy (now fixed) */
#include <stdio.h>

int unsorted[] = {25,16,30,5,28,27,9,13,23,26,2,29,3,11,17,7,0,21,19,24,4,8,22,12,10,18,15,20,14,6,1,31};

typedef int TYPE ;
static inline int compare(const void *a, const void *b)
{
  const TYPE da = *((const TYPE *) a);
  const TYPE db = *((const TYPE *) b);
  /* DECREASING sort */
  return (da < db) ? 1 : (da == db) ? 0 : -1;
}

int main(int argc, char *argv[])
{
  int err, i;
  char *sep = "";

  err = timsort(unsorted, sizeof(unsorted)/sizeof(unsorted[0]), sizeof(unsorted[0]), compare);
  if (err) {
    fprintf(stderr, "timsort returned error %d\n", err);
  } else {
    for (i =0; i < (sizeof(unsorted)/sizeof(unsorted[0])); ++i) {
      fprintf(stdout, "%s%d", sep, unsorted[i]);
      sep = " ";
    }
  }
  return 0;
}
