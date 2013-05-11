function driver(newCount, oldCount){
  assume(newCount != oldCount);
  var lock = 0;
  while (newCount != oldCount){
    invariant(lock == 1 || newCount != oldCount);
    lock = 1;
    oldCount = newCount;
    if (0 < newCount){
      lock     = 0;
      newCount = newCount - 1;
    }
  };
  assert(lock != 0);
}
