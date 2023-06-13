long p1 (long x1, long x2, long x3) {
  long y = x1 - x3;
  y = y + x2;
  return y;
}

long p2 (long x1, long x2, long x3) {
  long y1 = 0;
  long y2 = 0;
  long y3 = 0;
  if ((x1 >= 0) == (x3 >= 0)) {
    y1 = x1 - x3;
    y1 = y1 + x2;
    return y1;
  } else if ((x1 >= 0) != (x2 >= 0)) {
    y2 = x1 + x2;
    y2 = y2 - x3;
    return y2;
  } else {
    y3 = x2 - x3;
    y3 = y3 + x1;
    return y3;
  }
}
