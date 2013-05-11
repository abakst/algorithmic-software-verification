
function adpcm(n){
  assume(n > 0);
  var nsamples   = 2 * n;
  var inp0       = 0;
  var outp0      = 0;
  var inp        = inp0;
  var outp       = outp0;
  var bufferstep = 1;
  var len        = nsamples;
  while (0 < len) {
    invariant(inp0  == 0);
    invariant(outp0 == 0);
    invariant(inp0 <= inp);
    invariant(outp0 <= outp);
    invariant(inp == nsamples - len);
    invariant((bufferstep == 0) || (bufferstep == 1));
    invariant((2*outp - bufferstep) < inp);
    assert((inp0 <= inp) && (inp  <  inp0 + nsamples));
    inp = inp + 1;
    if (bufferstep == 0){
      assert ((2 * (outp - outp0)) <= (nsamples + 1)); 
      outp = outp + 1;
    } 
    bufferstep = 1 - bufferstep;
    len = len - 1;
  }
  return 0;
}


