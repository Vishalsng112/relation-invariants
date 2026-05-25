// method BubbleSortProduct(a: array<int>, a_prime: array<int>, N: int)
//     requires a != null && a_prime != null
//     requires a.Length == N && a_prime.Length == N
//     modifies a, a_prime
// {
//     var i := 0;
//     var i_prime := 0;

//     while (i < N)
//     invariant 0 <= i <= N
//     invariant i == i_prime
//     // invariant forall k, l :: N - i <= k < l < N ==> a[k] <= a[l]
//     // invariant forall k, l :: N - i <= k < l < N ==> a_prime[k] <= a_prime[l]
//     // invariant forall k, l :: 0 <= k < N - i && N - i <= l < N ==> a[k] <= a[l]
//     // invariant forall k, l :: 0 <= k < N - i && N - i <= l < N ==> a_prime[k] <= a_prime[l]
//     {
//         var j := N - 1;
//         var j_prime := N - 1;

//         while (j > i)
//         invariant i <= j <= N - 1
//         invariant j == j_prime
//         // // Bubble-up progress: a[j] is the max of a[i..j]
//         // invariant forall k :: i <= k <= j ==> a[k] <= a[j]
//         // invariant forall k :: i <= k <= j ==> a_prime[k] <= a_prime[j_prime]

//         // // Sorted suffix is preserved (outer invariant maintained)
//         // invariant forall k, l :: N - i <= k < l < N ==> a[k] <= a[l]
//         // invariant forall k, l :: N - i <= k < l < N ==> a_prime[k] <= a_prime[l]

//         // // Cross-boundary: unsorted prefix ≤ sorted suffix
//         // invariant forall k, l :: 0 <= k < N - i && N - i <= l < N ==> a[k] <= a[l]
//         // invariant forall k, l :: 0 <= k < N - i && N - i <= l < N ==> a_prime[k] <= a_prime[l]

//         {
//             if (a[j - 1] > a[j])
//             {
//                 // swap(a, j, j-1)
//                 var temp := a[j];
//                 a[j] := a[j - 1];
//                 a[j - 1] := temp;
//             }

//             if (a_prime[j_prime - 1] > a_prime[j_prime])
//             {
//                 // swap(a_prime, j_prime, j_prime-1)
//                 var temp_prime := a_prime[j_prime];
//                 a_prime[j_prime] := a_prime[j_prime - 1];
//                 a_prime[j_prime - 1] := temp_prime;
//             }

//             j := j - 1;
//             j_prime := j_prime - 1;
//         }

//         i := i + 1;
//         i_prime := i_prime + 1;
//     }
// }



// // ============================================================
// //  Induction Variable Strength Reduction — Product Program
// //  Relational invariant: i == i' /\ j' == i*B + C /\ x == x'
// // ============================================================

// method StrengthReduction(N: int, B: int, C: int)
//     requires N >= 0
// {
//     // ---------- Source program variables ----------
//     var i  : int := 0;
//     var j  : int := 0;
//     var x  : int := 0;

//     // ---------- Optimized program variables -------
//     var i' : int := 0;
//     var j' : int := C;
//     var x' : int := 0;

//     // ---------- Product program loop --------------
//     while (i < N && i' < N)

//         // ── Loop termination ──────────────────────
//         decreases N - i

//         // ── Relational Invariant (I_R) ────────────
//         //   (1)  i  == i'          (counters in sync)
//         //   (2)  j' == i * B + C   (simulation relation / key strength-reduction witness)
//         //   (3)  x  == x'          (accumulated sums equal)
//         invariant i == i'
//         invariant j' == i * B + C
//         invariant x  == x'

//         // ── Range invariants ─────────────────────
//         invariant 0 <= i  <= N
//         invariant 0 <= i' <= N
//     {
//         // ── Source program body ───────────────────
//         j  := i * B + C;   // strength-expensive multiply
//         x  := x + j;
//         i  := i + 1;

//         // ── Optimized program body ────────────────
//         x' := x' + j';     // cheap addition instead
//         j' := j' + B;
//         i' := i' + 1;
//     }

//     // ── Post-condition follows from I_R ∧ ¬guard ─
//     //   guard false  =>  i >= N /\ i' >= N
//     //   I_R(3)       =>  x == x'   (semantic equivalence)
//     assert x == x';
// }



// ============================================================
//  Loop Alignment — Product Program (Fig. 7)
//
//  Source program:
//      i := 1;
//      while (i <= N) do
//          b[i] := a[i];
//          d[i] := b[i-1];
//          i++
//
//  Transformed program:
//      j := 1; d_bar[1] := b_bar[0];
//      while (j <= N-1) do
//          b_bar[j] := a_bar[j];
//          d_bar[j+1] := b_bar[j];
//          j++
//      b_bar[N] := a_bar[N]
//
//  Post-condition:  d[1..N] == d_bar[1..N]
//
//  Relational Invariants:
//      (1)  i == j                          counters in sync
//      (2)  b[0..i-1] == b_bar[0..i-1]     b prefixes equal
//      (3)  d[1..i]   == d_bar[1..i]        d prefixes equal
// ============================================================

// method LoopAlignment(N: int,
//                      a:     seq<int>,   // source input array  (0-indexed, length N+1)
//                      a_bar: seq<int>)   // transformed input array (0-indexed, length N+1)
//     requires N >= 1
//     requires |a|     == N + 1
//     requires |a_bar| == N + 1
//     // Pre-condition from product program: a == a_bar /\ b[0] == b_bar[0]
//     requires a == a_bar
// {
//     // ---------- Source program variables ----------
//     var b  : array<int> := new int[N + 1];
//     var d  : array<int> := new int[N + 1];

//     // ---------- Transformed program variables -----
//     var b_bar : array<int> := new int[N + 1];
//     var d_bar : array<int> := new int[N + 1];

//     // ---------- Shared initial value of b[0] / b_bar[0] ----------
//     // (pre-condition: b[0] == b_bar[0]; we set both to 0 as a concrete witness)
//     b[0]     := 0;
//     b_bar[0] := 0;

//     // ---------- Product program initialisation ----------
//     var i : int := 1;
//     var j : int := 1;

//     // First iteration of source (align prologue)
//     assert i <= N;
//     b[i]     := a[i];
//     d[i]     := b[i - 1];
//     i        := i + 1;

//     // Transformed prologue: d_bar[1] := b_bar[0]
//     d_bar[1] := b_bar[0];

//     // Sync assertion before main loop
//     assert i == j + 1;   // i has advanced one step ahead of j

//     // ---------- Product program main loop ----------
//     // We re-align: after source's first step i==2, transformed starts j==1.
//     // Re-set to lock-step from here: drive both with a single counter k.
//     // We use i for the source (already at 2) and j for transformed (at 1).

//     while (i <= N)
//         decreases N - i + 1

//         // ── Relational Invariants ─────────────────
//         // (1) counters: source is one ahead of transformed
//         invariant j == i - 1

//         // (2) range
//         invariant 1 <= i <= N + 1
//         invariant 1 <= j <= N

//         // (3) b prefixes agree up to j (= i-1)
//         // invariant forall k :: 0 <= k <= j ==> b[k] == b_bar[k]

//         // (4) d prefixes agree up to i-1 (= j)
//         invariant forall k :: 1 <= k <= j ==> d[k] == d_bar[k]

//         // (5) b values match the input arrays (copied correctly)
//         invariant forall k :: 1 <= k <= j ==> b[k] == a[k]
//         // invariant forall k :: 1 <= k <= j ==> b_bar[k] == a_bar[k]
//     {
//         // ── Source body ───────────────────────────
//         b[i]     := a[i];
//         d[i]     := b[i - 1];
//         i        := i + 1;

//         // ── Transformed body ─────────────────────
//         b_bar[j] := a_bar[j];
//         d_bar[j + 1] := b_bar[j];
//         j        := j + 1;

//         // ── Sync assertion inside loop ────────────
//         assert j == i - 1;
//     }

//     // ---------- Transformed epilogue ----------
//     b_bar[N] := a_bar[N];

//     // ---------- Post-condition ------------------
//     // d[1..N] == d_bar[1..N]
//     assert forall k :: 1 <= k <= N ==> d[k] == d_bar[k];
// }


// // E1 program:
// method ProgramProduct(N: int, B: int, C: int)
//     returns (x: int, x': int)
//     requires N >= 0
//     ensures x == x'
// {
//     var i  := 0;
//     var i' := 0;
//     var j' := C;
//     var j  := 0;
//     x  := 0;
//     x' := 0;

//     while (i < N && i' < N)
//         invariant i == i'
//         invariant j' == i' * B + C
//         invariant x == x'
//         invariant 0 <= i <= N
//     {
//         // Source program step
//         j  := i * B + C;
//         x  := x  + j;
//         i  := i  + 1;

//         // Optimized program step
//         x' := x' + j';
//         j' := j' + B;
//         i' := i' + 1;
//     }
// }

// // E2 program:
// method Product(N: int) returns (x: int, y: int)
//   requires N >= 0
//   ensures x == y
// {
//     x := 0;
//     var i := 0;
//     x := x + i;
//     i := i + 1;
//     var j := 1;
//     y := 0;
//     while i <= N
//         invariant i == j           // structural sync between i and j
//         invariant x == y           // relational invariant (key)
//         // invariant i >= 1
//         // invariant i <= N + 1
//         // invariant x == i * (i - 1) / 2   // arithmetic witness
//     {
//         y := y + j;
//         j := j + 1;
//         x := x + i;
//         i := i + 1;
//     }
// }






// E3 program: Loop Alignment product program (Fig. 7) of the paper.
// method LoopAlignment(
//     a    : array<int>,
//     aBar : array<int>,
//     N    : int)
//     returns (
//         b    : array<int>,
//         bBar : array<int>,
//         d    : array<int>,
//         dBar : array<int>)

//     requires N >= 1
//     requires a.Length    == N + 1
//     requires aBar.Length == N + 1
//     requires forall k :: 0 <= k <= N ==> a[k] == aBar[k]
//     ensures  b.Length    == N + 1
//     ensures  bBar.Length == N + 1
//     ensures  d.Length    == N + 1
//     ensures  dBar.Length == N + 1
//     // Postcondition
//     ensures  forall k :: 1 <= k <= N ==> d[k] == dBar[k]
// {
//     b    := new int[N + 1];
//     bBar := new int[N + 1];
//     d    := new int[N + 1];
//     dBar := new int[N + 1];

//     // Establish b[0] = b_bar[0] from precondition a = a_bar
//     b[0]    := a[0];
//     bBar[0] := aBar[0];

//     // ── Prologue 
//     var i := 1;
//     var j := 1;

//     assert i <= N;
//     // Source: first iteration runs alone
//     b[i] := a[i];
//     d[i] := b[i - 1];
//     i    := i + 1;

//     // Transformed: paired init step
//     dBar[1] := bBar[0];

//     // Alignment sync assertion (Fig. 7): assert(i ≤ N <==> j ≤ N−1)
//     assert (i <= N) == (j <= N - 1);

//     while i <= N
//     invariant i == j + 1
//     invariant 2 <= i <= N + 1
//     invariant 1 <= j <= N
//     invariant forall k :: 1 <= k < i ==> b[k] == a[k]
//     invariant forall k :: 1 <= k < i ==> d[k] == b[k - 1]
//     invariant forall k :: 1 <= k < i ==> d[k] == dBar[k]
//     {
//         // ── Source step
//         b[i] := a[i];
//         d[i] := b[i - 1];
//         i    := i + 1;

//         // ── Transformed step 
//         bBar[j] := aBar[j];
//         dBar[j + 1] := bBar[j];
//         j    := j + 1;

//         assert (i <= N) == (j <= N - 1);
//     }

//     bBar[N] := aBar[N];
// }


// // E4 program:
// method ProductProgram(
//     N      : int,
//     a      : array<int>,  // source arrays
//     b      : array<int>,
//     c      : array<int>,
//     a_bar  : array<int>,  // transformed (pipelined) arrays
//     b_bar  : array<int>,
//     c_bar  : array<int>
// )
//     // Paper states: "assume a, b, c are arrays of size N, with 2 <= N"
//     requires N >= 2
//     requires a.Length == N && b.Length == N && c.Length == N
//     requires a_bar.Length == N && b_bar.Length == N && c_bar.Length == N

//     // No aliasing between any pair of arrays
//     requires a != b && a != c && a != a_bar && a != b_bar && a != c_bar
//     requires b != c && b != a_bar && b != b_bar && b != c_bar
//     requires c != a_bar && c != b_bar && c != c_bar
//     requires a_bar != b_bar && a_bar != c_bar
//     requires b_bar != c_bar

//     modifies a, b, c, a_bar, b_bar, c_bar

//     // ── Pre-condition: { a = a_bar /\ b = b_bar /\ c = c_bar } ──────────
//     requires forall k :: 0 <= k < N ==> a[k] == a_bar[k]
//     requires forall k :: 0 <= k < N ==> b[k] == b_bar[k]
//     requires forall k :: 0 <= k < N ==> c[k] == c_bar[k]

//     // ── Post-condition: { a = a_bar /\ b = b_bar /\ c = c_bar } ─────────
//     ensures forall k :: 0 <= k < N ==> a[k] == a_bar[k]
//     ensures forall k :: 0 <= k < N ==> b[k] == b_bar[k]
//     ensures forall k :: 0 <= k < N ==> c[k] == c_bar[k]
// {

//     var i := 0;
//     var j := 0;

//     assert i < N;

//     // ── Source: first iteration (i = 0) ─────────────────────────────────
//     a[i] := a[i]    + 1;
//     b[i] := b[i]    + a[i];
//     c[i] := c[i]    + b[i];
//     i := i + 1;

//     a_bar[0] := a_bar[0] + 1;
//     b_bar[0] := b_bar[0] + a_bar[0];

//     assert i < N;

//     a[i]    := a[i]    + 1;
//     b[i]    := b[i]    + a[i];
//     c[i]    := c[i]    + b[i];
//     i       := i + 1;


//     a_bar[1] := a_bar[1] + 1;

//     assert (i < N) == (j < N - 2);

//     while i < N
//     invariant 0 <= j && i == j + 2 && j <= N - 2

//     // ── Source array state ────────────────────────────────────────────────
//     // Source loop has processed indices 0..i-1 already
//     invariant forall k :: 0 <= k < i ==>
//         a[k] == old(a[k]) + 1

//     invariant forall k :: 0 <= k < i ==>
//         b[k] == old(b[k]) + (old(a[k]) + 1)

//     invariant forall k :: 0 <= k < i ==>
//         c[k] == old(c[k]) + (old(b[k]) + (old(a[k]) + 1))

//     // Source is unchanged for indices i..N-1
//     invariant forall k :: i <= k < N ==>
//         a[k] == old(a[k]) && b[k] == old(b[k]) && c[k] == old(c[k])

//     // ── Bar array state (pipelined, 2-cycle lag) ─────────────────────────

//     // Stage A: a_bar is done for indices 0..j+1 (two ahead of c_bar)
//     invariant forall k :: 0 <= k <= j + 1 ==>
//         a_bar[k] == old(a_bar[k]) + 1

//     invariant forall k :: j + 2 <= k < N ==>
//         a_bar[k] == old(a_bar[k])

//     // Stage B: b_bar is done for indices 0..j (one ahead of c_bar)
//     invariant forall k :: 0 <= k <= j ==>
//         b_bar[k] == old(b_bar[k]) + (old(a_bar[k]) + 1)

//     invariant forall k :: j + 1 <= k < N ==>
//         b_bar[k] == old(b_bar[k])

//     // Stage C: c_bar is done for indices 0..j-1
//     invariant forall k :: 0 <= k < j ==>
//         c_bar[k] == old(c_bar[k]) + (old(b_bar[k]) + (old(a_bar[k]) + 1))

//     invariant forall k :: j <= k < N ==>
//         c_bar[k] == old(c_bar[k])
//     {
//         //Source loop body
//         a[i] := a[i] + 1;
//         b[i] := b[i] + a[i];
//         c[i] := c[i] + b[i];
//         i := i + 1;

//         // ── Transformed loop body 
//         a_bar[j + 2] := a_bar[j + 2] + 1;
//         b_bar[j + 1] := b_bar[j + 1] + a_bar[j + 1];
//         c_bar[j] := c_bar[j]     + b_bar[j];
//         j := j + 1;

//         // assert(i < N  <=>  j < N-2)  [inside loop, Fig. 6]
//         assert (i < N) == (j < N - 2);
//     }
//     c_bar[j] := c_bar[j]     + b_bar[j];
//     b_bar[j + 1] := b_bar[j + 1] + a_bar[j + 1];
//     c_bar[j + 1] := c_bar[j + 1] + b_bar[j + 1];
// }


// // E8 program
method ProductProgram(a: array2<int>, N: int, M: int, L: int)
  returns (s: array<int>, t: array<int>)
  requires M <= N
  requires N >= 0 && M >= 1 && L >= 1
  requires a.Length0 == N + 1 && a.Length1 == L
  ensures s.Length == N - M + 1
  ensures t.Length == N - M + 1
  ensures forall i :: 0 <= i <= N - M ==> s[i] == t[i]
{
  s := new int[N - M + 1];
  t := new int[N - M + 1];
  var b := new int[N + M];

  var i1 := 0;
  assert i1 <= N - M;
  s[i1] := 0;
  var k1 := 0;
  t[0] := 0;
  var k2 := 0;
  assert k1 <= M - 1 <==> k2 <= M - 1;

  while k1 <= M - 1
    invariant k1 == k2
    invariant 0 <= k1 <= M
    invariant i1 == 0
    invariant s.Length == N - M + 1
    invariant t.Length == N - M + 1
    invariant b.Length == N + M
    invariant t[0] == s[i1]
    // invariant s[i1] == (var acc := 0; acc) + (
    //   if k1 == 0 then 0
    //   else
    //     (var sum := 0; sum)
    // )
    // invariant forall kk :: 0 <= kk < k1 ==>
    //   b[kk] == (var rowsum := 0; rowsum) +
    //     (var lsum := 0; lsum)
    invariant t[0] == s[0]
  {
    var l1 := 0;
    b[k2] := 0;
    var l2 := 0;
    assert l1 <= L - 1 <==> l2 <= L - 1;

    while l1 <= L - 1
      invariant l1 == l2
      invariant 0 <= l1 <= L
      invariant k1 == k2
      invariant 0 <= k1 < M
      invariant i1 == 0
      invariant s.Length == N - M + 1
      invariant t.Length == N - M + 1
      invariant b.Length == N + M
      invariant s[i1] - b[k2] == t[0]
    {
      s[i1] := s[i1] + a[i1 + k1, l1];
      l1 := l1 + 1;
      b[k2] := b[k2] + a[k2, l2];
      l2 := l2 + 1;
      assert l1 <= L - 1 <==> l2 <= L - 1;
    }

    k1 := k1 + 1;
    t[0] := t[0] + b[k2];
    k2 := k2 + 1;
    assert k1 <= M - 1 <==> k2 <= M - 1;
  }

  i1 := i1 + 1;
  var i2 := 1;
  assert i1 <= N - M <==> i2 <= N - M;

  while i1 <= N - M
    invariant i1 == i2
    invariant 1 <= i1 <= N - M + 1
    invariant s.Length == N - M + 1
    invariant t.Length == N - M + 1
    invariant b.Length == N + M
    // invariant forall idx :: 0 <= idx < i1 ==> s[idx] == t[idx]
  {
    b[i2 + M - 1] := 0;
    var l2 := 0;

    while l2 <= L - 1
      invariant 0 <= l2 <= L
      invariant i1 == i2
      invariant 1 <= i1 <= N - M
      invariant s.Length == N - M + 1
      invariant t.Length == N - M + 1
      invariant b.Length == N + M
      invariant forall idx :: 0 <= idx < i1 ==> s[idx] == t[idx]
    {
      b[i2 + M - 1] := b[i2 + M - 1] + a[i2 + M - 1, l2];
      l2 := l2 + 1;
    }

    var z := b[i2 + M - 1] - b[i2 - 1];
    t[i2] := t[i2 - 1] + z;
    i2 := i2 + 1;

    s[i1] := 0;
    var k1 := 0;

    while k1 <= M - 1
      invariant 0 <= k1 <= M
      invariant 1 <= i1 <= N - M
      invariant i2 == i1 + 1
      invariant s.Length == N - M + 1
      invariant t.Length == N - M + 1
      invariant b.Length == N + M
      invariant forall idx :: 0 <= idx < i1 ==> s[idx] == t[idx]
    {
      var l1 := 0;

      while l1 <= L - 1
        invariant 0 <= l1 <= L
        invariant 0 <= k1 < M
        invariant 1 <= i1 <= N - M
        invariant i2 == i1 + 1
        invariant s.Length == N - M + 1
        invariant t.Length == N - M + 1
        invariant b.Length == N + M
        invariant forall idx :: 0 <= idx < i1 ==> s[idx] == t[idx]
      {
        s[i1] := s[i1] + a[i1 + k1, l1];
        l1 := l1 + 1;
      }

      k1 := k1 + 1;
    }

    i1 := i1 + 1;
    assert i1 <= N - M <==> i2 <= N - M;
  }
}