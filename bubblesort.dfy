function Abs(x: int): int
{
  if x >= 0 then x else -x
}


method Swap(a: array<int>, p: int, q: int)
  requires 0 <= p < a.Length
  requires 0 <= q < a.Length
  modifies a
  ensures  a[p] == old(a[q])
  ensures  a[q] == old(a[p])
  ensures  forall k :: 0 <= k < a.Length && k != p && k != q ==> a[k] == old(a[k])
{
  var tmp := a[p];
  a[p] := a[q];
  a[q] := tmp;
}


method BubbleSortProduct(a: array<int>, a': array<int>, ghost eps: int)
  requires a != a'
  requires a.Length == a'.Length
  requires eps > 0
  requires forall i :: 0 <= i < a.Length ==> Abs(a[i] - a'[i]) < eps
  modifies a, a'
  ensures  forall i :: 0 <= i < a.Length ==> Abs(a[i] - a'[i]) < eps
{
  var N := a.Length;
  var i := 0;
  var i_bar := 0;

  while i < N
    invariant i == i_bar
    invariant 0 <= i <= N
    invariant forall k :: 0 <= k < a.Length ==> Abs(a[k] - a'[k]) < eps
  {
    var j := N - 1;
    var j_bar := N - 1;
    while j > i
      invariant j == j_bar
      invariant i <= j <= N - 1
      invariant forall k :: 0 <= k < a.Length ==> Abs(a[k] - a'[k]) < eps
    {
      if a[j - 1] > a[j] {
        Swap(a, j, j - 1);
      }

      if a'[j_bar - 1] > a'[j_bar] {
        Swap(a', j_bar, j_bar - 1);
      }

      j := j - 1;
      j_bar := j_bar - 1;
    }

    i := i + 1;
    i_bar := i_bar + 1;
  }
}