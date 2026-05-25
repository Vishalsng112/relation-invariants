method ProductProgram(a: array<int>, ap: array<int>, N: int)
  requires N >= 1
  requires a.Length > N
  requires ap.Length > N
  requires a.Length == ap.Length
  requires forall k :: 0 <= k <= N ==> a[k] == ap[k]
  modifies a, ap
  ensures forall k :: 0 <= k <= N ==> a[k] == ap[k]
{
  // Source side init
  var max := a[0];
  var maxi := 0;
  var i := 0;

  // Product side init
  var maxp := ap[0];
  var maxip := 0;
  var j := 0;

  assert i <= N;
  if (max < a[i]) { max := a[i]; maxi := i; }
  i := i + 1;

  assert j <= N;
  assert j == 0;
  if (j == 0) { maxp := ap[0]; maxip := 0; }
  if (maxp < ap[j]) { maxp := ap[j]; maxip := j; }
  assert j != N;

  assert (i <= N && i != N) <==> (j <= N && j != N);

  while (i <= N && i != N)
    invariant 1 <= i <= N
    invariant 1 <= j <= N
    invariant i == j
    invariant max == maxp
    invariant maxi == maxip
    invariant forall k :: 0 <= k <= N ==> a[k] == ap[k]
    decreases N - i
  {
    assert j != 0;
    if (max < a[i]) { max := a[i]; maxi := i; }
    if (maxp < ap[j]) { maxp := ap[j]; maxip := j; }
    assert j != N;
    j := j + 1;
    i := i + 1;
    assert (i <= N && i != N) <==> (j <= N && j != N);
  }

  assert i == N;
  assert j == N;
  assert j != 0;

  if (max < a[i]) { max := a[i]; maxi := i; }
  if (maxp < ap[j]) { maxp := ap[j]; maxip := j; }
  i := i + 1;

  assert j == N;
  var tp := ap[N];
  ap[N] := maxp;
  ap[maxip] := tp;
  j := j + 1;

  var t := a[N];
  a[N] := max;
  a[maxi] := t;

}