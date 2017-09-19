module IntProgs

data IntTree = leaf() | inode(IntTree left, int val, IntTree right);


int abs(int x) {
  if (x < 0) -x;
  else x;
}

IntTree abstree(IntTree t) = bottom-up visit (t) {
  case leaf() => leaf()
  case inode(l,v,r) => inode(l, abs(v), r)
};

list[int] evenedout() {
  list[int] xs = [1,2,3,5,7,13];
  list[int] ys = [];
  for (x <- xs)
     ys = [x*2] + ys;
  return ys;
}