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

method LoopAlignment(N: int,
                     a:     seq<int>,   // source input array  (0-indexed, length N+1)
                     a_bar: seq<int>)   // transformed input array (0-indexed, length N+1)
    requires N >= 1
    requires |a|     == N + 1
    requires |a_bar| == N + 1
    // Pre-condition from product program: a == a_bar /\ b[0] == b_bar[0]
    requires a == a_bar
{
    // ---------- Source program variables ----------
    var b  : array<int> := new int[N + 1];
    var d  : array<int> := new int[N + 1];

    // ---------- Transformed program variables -----
    var b_bar : array<int> := new int[N + 1];
    var d_bar : array<int> := new int[N + 1];

    // ---------- Shared initial value of b[0] / b_bar[0] ----------
    // (pre-condition: b[0] == b_bar[0]; we set both to 0 as a concrete witness)
    b[0]     := 0;
    b_bar[0] := 0;

    // ---------- Product program initialisation ----------
    var i : int := 1;
    var j : int := 1;

    // First iteration of source (align prologue)
    assert i <= N;
    b[i]     := a[i];
    d[i]     := b[i - 1];
    i        := i + 1;

    // Transformed prologue: d_bar[1] := b_bar[0]
    d_bar[1] := b_bar[0];

    // Sync assertion before main loop
    assert i == j + 1;   // i has advanced one step ahead of j

    // ---------- Product program main loop ----------
    // We re-align: after source's first step i==2, transformed starts j==1.
    // Re-set to lock-step from here: drive both with a single counter k.
    // We use i for the source (already at 2) and j for transformed (at 1).

    while (i <= N)
        decreases N - i + 1

        // ── Relational Invariants ─────────────────
        // (1) counters: source is one ahead of transformed
        invariant j == i - 1

        // (2) range
        invariant 1 <= i <= N + 1
        invariant 1 <= j <= N

        // (3) b prefixes agree up to j (= i-1)
        // invariant forall k :: 0 <= k <= j ==> b[k] == b_bar[k]

        // (4) d prefixes agree up to i-1 (= j)
        invariant forall k :: 1 <= k <= j ==> d[k] == d_bar[k]

        // (5) b values match the input arrays (copied correctly)
        invariant forall k :: 1 <= k <= j ==> b[k] == a[k]
        // invariant forall k :: 1 <= k <= j ==> b_bar[k] == a_bar[k]
    {
        // ── Source body ───────────────────────────
        b[i]     := a[i];
        d[i]     := b[i - 1];
        i        := i + 1;

        // ── Transformed body ─────────────────────
        b_bar[j] := a_bar[j];
        d_bar[j + 1] := b_bar[j];
        j        := j + 1;

        // ── Sync assertion inside loop ────────────
        assert j == i - 1;
    }

    // ---------- Transformed epilogue ----------
    b_bar[N] := a_bar[N];

    // ---------- Post-condition ------------------
    // d[1..N] == d_bar[1..N]
    assert forall k :: 1 <= k <= N ==> d[k] == d_bar[k];
}