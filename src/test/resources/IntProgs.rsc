module IntProgs

data IntTree = leaf() | inode(IntTree left, int val, IntTree right);

list[int] evenedout() {
  list[int] xs = [1,2,3,5,7,13];
  list[int] ys = [];
  for (x <- xs)
     ys = [x*2] + ys;
  return ys;
}