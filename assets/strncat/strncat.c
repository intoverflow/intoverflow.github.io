#define char int
typedef unsigned int size_t;

size_t strlen(const char *s) {
  size_t i;
  char c;

  i = 0;
  c = s[i];
  while ('\0' != c) {
    i++;
    c = s[i];
  }

  return i;
}

char *strncat(char *dest, const char *src, size_t n) {
  size_t dest_len = strlen(dest);
  size_t i;

  for (i = 0; i < n && src[i] != 0; i++)
    dest[dest_len + i] = src[i];
  dest[dest_len + i] = 0;

  return dest;
}

