# Homework: answers

Name(s):

## OpenJML

### 1. Absolute

Q: What does OpenJML complain about before you write a contract, and for which input?

A: 
The OpenJML complain following:

$ openjml --esc hw/Absolute.java
hw/Absolute.java:9: verify: The prover cannot establish an assertion (ArithmeticOperationRange) in method abs: int negation
            return -n;
                   ^
1 verification failure
NOT VERIFIED: see the messages above

The ArithmeticOperationRange means there exists a potential int overflow. This happens for input n = Integer.MIN_VALUE = -(2^31).


Q: Which `requires` did you need, and why? Could you avoid it by changing the `ensures`?

A:
I need following requirement:
'//@ requires n != Integer.MIN_VALUE;'

Logically, it seems like we can avoid the overflow problem by '//@ ensures \result >= 0;'. But the warnning is comming from the Java Arithmetic Operation itself, has nothing to do with what I claim the result should be. 

If we only add '//@ ensures \result >= 0;', we will get following:

$ openjml --esc hw/Absolute.java
hw/Absolute.java:9: verify: The prover cannot establish an assertion (ArithmeticOperationRange) in method abs: int negation
            return -n;
                   ^
hw/Absolute.java:9: verify: The prover cannot establish an assertion (Postcondition: hw/Absolute.java:6:) in method abs
            return -n;
            ^
hw/Absolute.java:6: verify: Associated declaration: hw/Absolute.java:9:
    //@ ensures \result >= 0;
        ^
3 verification failures
NOT VERIFIED: see the messages above

It will even add another warning about Postcondition.

Thus the answer is no.

### 2. SumX

Q: Which proof obligations fail? Is the program wrong?

A:
The OpenJML complain following:

$ openjml --esc hw/SumX.java
hw/SumX.java:16: verify: The prover cannot establish an assertion (Postcondition: hw/SumX.java:6:) in method sum
        return s;
        ^
hw/SumX.java:6: verify: Associated declaration: hw/SumX.java:16:
    //@ ensures \result == x * (x + 1) / 2;
        ^
hw/SumX.java:14: verify: The prover cannot establish an assertion (ArithmeticOperationRange) in method sum: overflow in int sum
            s = s + i;
                  ^
3 verification failures
NOT VERIFIED: see the messages above

Failing obligations:
1.Postcondition:'//@ ensures \result == x * (x + 1) / 2;' fails.
2.ArithmeticOperationRange (s = s + 1) fails.

The program is not wrong. The first warning says it might happens that s != x * (x + 1) /2. An example is s is negative. The second warning says there might exist integer overflow for s = s + i. An example is: s = Integer.MAX_VALUE. The JML believes these are possible since we didn't write any requirements about s.

Q: Largest N for which `x <= N` verifies? What happens with N + 1, and why?

A:
The largest N is 65535. We have 65535 * 65536 / 2 = 2,147,450,880 < Integer.MAX_VALUE = 2,147,483,647, 655356 * 65537 / 2 = 2,147,516,416 > Integer.MAX_VALUE = 2,147,483,647, thus with 65536 we have overflow.

### 3. Max

Q: Is the remaining failure caused by your invariants or by the code? (Your hypothesis.)

A: That is caused by the code: 'for (int i = 1; i < a.length - 1; i++)'. It should be 'for (int i = 1; i < a.length; i++)', otherwise we cannot reach the last element.

### 4. BinarySearch

Q: What does OpenJML report, in which method, and for which concrete call? How large must the array be?

A:
$ openjml --esc hw/BinarySearch.java
hw/BinarySearch.java:8: verify: The prover cannot establish an assertion (ArithmeticOperationRange) in method midpoint: overflow in int sum
        return (lo + hi) / 2;
                   ^
hw/BinarySearch.java:8: verify: The prover cannot establish an assertion (Postcondition: hw/BinarySearch.java:6:) in method midpoint
        return (lo + hi) / 2;
        ^
hw/BinarySearch.java:6: verify: Associated declaration: hw/BinarySearch.java:8:
    //@ ensures lo <= \result && \result <= hi;
        ^
3 verification failures
NOT VERIFIED: see the messages above

First, ArithmeticOperationRange said there exists a potential overflow in the 'return (lo + hi) / 2;' in method 'int midpoint', a counterexample is lo = 1, hi = 2147483647 = Integer_MAX_VALUE with '//@ requires 0 <= lo && lo <= hi;' holds true.

Second, Posecondition said '//@ ensures lo <= \result && \result <= hi;' might not be true in method 'int midpoint', a counterexample is same to the overflow one we have in the first complaint.

Thus, a concrete call is midpoint(1, 2147483647).

When the size of array is N, we have lo = 0, hi = N - 1. Then it might happen that after the loop we get lo = hi = N - 1, then lo + hi = 2N - 2. If 2N - 2 > Integer_MAX_VALUE, then N > (Integer_MAX_VALUE + 2) / 2. Thus, when the array has size > (Integer_MAX_VALUE + 2) / 2, we get an overflow and the above complaints.


Q: What happens without `/*@ pure @*/` on `midpoint`, and why?

A:
Besides previous complaints, we have the followings:
        ^
hw/BinarySearch.java:21: verify: The prover cannot establish an assertion (Assignable: hw/BinarySearch.java:20:) in method search: \everything
            int mid = midpoint(lo, hi);
                              ^
hw/BinarySearch.java:20: verify: Associated declaration: hw/BinarySearch.java:21:
        while (lo <= hi) {
        ^
hw/BinarySearch.java:18: verify: The prover cannot establish an assertion (LoopInvariant) in method search
        //@ loop_invariant (\forall int j; hi < j && j < a.length; a[j] > key);
            ^
hw/BinarySearch.java:17: verify: The prover cannot establish an assertion (LoopInvariant) in method search
        //@ loop_invariant (\forall int j; 0 <= j && j < lo; a[j] < key);
            ^
7 verification failures

This is because `/*@ pure @*/` ensures that the method 'int midpoint' does not modify any memory locations. If we remove that, the calling of 'midpoint(lo, hi)' might change the array a. As in the report, we have "The prover cannot establish an assertion (Assignable: hw/BinarySearch.java:20:) in method search: \everything", \everything says the method can modify everything.

Therefore, we also have next two complaints since a[j] might be not larger\smaller than key.

## JBMC

### 5. Max, again

Q: What input did JBMC find, and what goes wrong? Was your hypothesis of exercise 3 right?

A:
Input: a = {3, 32770}, `//@ ensures (\forall int j; 0 <= j && j < a.length; \result >= a[j]);` goes wrong. My hypothesis of exercise 3 was correct, the loop didn't go through all elements in the array.


Q: Smallest `--unwind` and `--max-nondet-array-length` that find it? Relation to the small scope hypothesis?

A:
Smallest `--unwind` is 2, smallest `--max-nondet-array-length` is 2.


Q: Why does `--unwind 5` with unwinding assertions fail on the fixed version? Smallest K with `--max-nondet-array-length 4`, and why not one less? What has been proved?

A:
Without `--no-unwinding-assertions`, after *K* iterations we have `assert !B`, that is, the loop breaks after K iterations. For `Max.java`, `for (int i = 1; i < a.length; i++) {` has 5 iterations before exit (i = 1, 2, 3, 4, 5, exits the loop when i = 5), then VERIFICATION SUCCESS. But for `MaxCheck.java`, `for (int j = 0; j < a.length; j++) {` has 6 iterations before exit since it starts at j = 0. Then `--unwind 5` is not enough, we don't have `assert !B` be true after 5 iterations.
With `--max-nondet-array-length 4`, the smallest K that gives VERIFICATION SUCCESS is 5. For K less than 5, we have for an array with length 4, the for loop: `for (int j = 0; j < a.length; j++) {` exits at the fifth iterations. Therefore we won't have `assert !B` holds true after *K* iterations.
For `./bmc MaxCheck.check --unwind 5 --max-nondet-array-length 4`, this has proved that `Max.java` returns max element for any array with max length 4 (a.length <= 4).

### 6. SumX

Q: Which values of `x` were checked with `--unwind 10 --no-unwinding-assertions`? Why does it fail with unwinding assertions? Which K is a proof? Sizes and times for K = 10, 100 and that K.

A:
x = 0, 1, 2 ,3, ..., 9 since `while(i < x)` has *x + 1* iterations, and `--unwind 10 --no-unwinding-assertions` means unroll every loop *K* times and after *K* iterations, `assume !B`, that is, only consider executions where `!B` holds, ignore the others. For ant x >= 10, we have `!B` fails.

If with unwinding assertions, we have `assert !B` after *K* iterations. Once x >= 10, the loop doesn't exit after 10 iterations. A counterexample gave by JBMC, `x = 33`, is in this case.

K = 1001 turns the result into a proof since `x <= 1000`.

Sizes and times:
$ jbmc SumXCheck.check --unwind 10 --no-unwinding-assertions

38 properties hold, 0 fail   (SAT formula: 4721 variables, 13723 clauses, solved in 0.00s)
VERIFICATION SUCCESSFUL

$ jbmc SumXCheck.check --unwind 100 --no-unwinding-assertions

38 properties hold, 0 fail   (SAT formula: 9670 variables, 30339 clauses, solved in 0.02s)
VERIFICATION SUCCESSFUL

$ jbmc SumXCheck.check --unwind 1001 --no-unwinding-assertions

38 properties hold, 0 fail   (SAT formula: 66953 variables, 666215 clauses, solved in 1.32s)
VERIFICATION SUCCESSFUL
┌──────────────────┬───────────────────────┬────────────────────┬──────────────────────┐
│    Comparison    │     SAT variavles     │      SAT clauses   │     solving time     │
├──────────────────┼───────────────────────┼────────────────────┼──────────────────────┤
│ K=10 →           │ 4721 → 9670           │ 13723 → 30339      │ 0.00 s → 0.02 s      │
│ K=100            │                       │                    |                      │
├──────────────────┼───────────────────────┼────────────────────┼──────────────────────┤
│ K=100 →          │ 9670 → 66953          │ 30339 →            │ 0.02 s → 1.32 s      │
│ K=1001           │                       │ 666215             │                      │
├──────────────────┼───────────────────────┼────────────────────┼──────────────────────┤
│ K=10 →           │ 4721 → 66953          │ 13723 →            │ 0.00s -> 1.32 s      │
│ K=1001           │                       │ 666215             │                      │
└──────────────────┴───────────────────────┴────────────────────┴──────────────────────┘

Q: What did OpenJML need from you, and what did JBMC need?

A:
OpenJML needs loop invariants from me, JBMC needs `--unwind K` from me. 

### 7. BinarySearch

Q: Why does JBMC miss the bug with the `search` harness? Could a larger bound help?

A:
The bug is from the overflow, but JBMC doesn't generate overflow property defaultly. The larger bound won't help.

Q: What did the `midpoint` harness find?

A:
$ jbmc BinarySearchCheck.midpoint --unwind 1
  FAILED  hw/BinarySearchCheck.java:38   assertion: assert mid;

39 properties hold, 1 fail   (SAT formula: 3145 variables, 4298 clauses, solved in 0.00s)
VERIFICATION FAILED

Counterexample for hw/BinarySearchCheck.java:38   assertion: assert mid;
------------------------------------------------------------------------
  BinarySearchCheck.midpoint  ← entry point
    line 28: lo = 131071
    line 28: hi = 2147418112
    line 30: mid = false
    line 32: call BinarySearch.midpoint
      line 32: lo = 131071
      line 32: hi = 2147418112
    line 32: midpoint = -1073709056
  ✗ line 38: assert mid;

It finds a counterexample with overflow, that is, lo = 131071, hi = 2147418112.


## Comparison

### 8. Comparison

| program | OpenJML: result, what you wrote | JBMC: result, bound used |
| --- | --- | --- |
| SumX | **OK** — wrote `loop_invariant 0 <= i && i <= x && s == i * (i + 1) / 2` and `decreases x - i`; no code change | **SUCCESSFUL** with `--unwind 1001` (with unwinding assertions): proof for all `0 <= x <= 1000`. `--unwind 10/100 --no-unwinding-assertions` only cover `x <= 9/99`. |
| Max | **OK** — fixed the loop to `i < a.length`; wrote invariants `0 < i && i <= a.length`, `m` is an element of `a[0..i-1]`, and `m >=` every element of `a[0..i-1]`, plus `decreases a.length - 1 - i`. | Bug found with `--unwind 3 --no-unwinding-assertions`: `a = {3, 32770}`; minimal bounds `K = 2`, `N = 2`. After the fix, **SUCCESSFUL** with `--unwind 5 --max-nondet-array-length 4`: proof for all arrays of length 1..4. |
| BinarySearch | Before fixing: reports `ArithmeticOperationRange` and `Postcondition` in `midpoint` for `lo + hi > Integer.MAX_VALUE` (via `search` this needs an array of length at least `2^30 + 1`). `pure` on `midpoint` is required; without it, `search` also gets `Assignable` and two `LoopInvariant` failures. After fixing `midpoint` (e.g. `lo + (hi - lo) / 2`): **OK**. | `search` harness `--unwind 6 --max-nondet-array-length 5`: **SUCCESSFUL**, but misses the bug. `midpoint` harness `--unwind 1`: **VERIFICATION FAILED**, e.g. `lo = 98299`, `hi = 2147418112`. After fixing `midpoint`: **SUCCESSFUL**. |

Note: the Max row assumes the stale invariant `i <= a.length - 1 || a.length == 1` is removed, and the BinarySearch row assumes `midpoint` is fixed.

Q: When would you use each tool?

A:
- **OpenJML (deductive verification)** when you need a proof for all inputs and can write contracts and loop invariants. It handles unbounded data and loops, checks JML obligations and Java arithmetic-range checks (e.g. the `midpoint` overflow), and supports modular reasoning with `pure` methods. The price is that you must find invariants; a failed proof can mean either a bug or an invariant that is too weak, and the tool does not give concrete inputs.
- **JBMC (bounded model checking)** when you want to find bugs quickly and get a concrete counterexample, especially for small-scope inputs, state machines, sequences of operations, and heap structures. You provide a harness and a bound `K`; JBMC automatically checks null dereferences, array bounds, division by zero and uncaught exceptions. The price is that `SUCCESSFUL` only covers executions within the bound (unless the bound provably covers all inputs), and large bounds make the SAT formula and solving time grow quickly.
- **Together**: use JBMC first to find a counterexample and understand a failure (e.g. `Max` with `a = {3, 32770}`), then OpenJML to prove the fixed code for all inputs (e.g. `SumX` with its invariant, and `BinarySearch` with the fixed `midpoint`); or use OpenJML to expose a bug that JBMC's bound hides (e.g. the `BinarySearch` overflow that needs an array of length about `2^30`).
