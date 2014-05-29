typedef unsigned int size_t;

size_t strlen(const unsigned char *s) {
  size_t i;
  unsigned char c;

  i = 0;
  c = s[i];
  while ('\0' != c) {
    i++;
    c = s[i];
  }

  return i;
}

unsigned char *strncat(unsigned char *dest, const unsigned char *src, size_t n) {
  size_t dest_len = strlen(dest);
  size_t i;

  for (i = 0; i < n && src[i] != 0; i++)
    dest[dest_len + i] = src[i];
  dest[dest_len + i] = 0;

  return dest;
}

