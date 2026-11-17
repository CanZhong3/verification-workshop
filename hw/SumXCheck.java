import org.cprover.CProver;

// 6. A harness for SumX.sum with the contract of exercise 2.
//   ./bmc SumXCheck.check --unwind 10 --no-unwinding-assertions
public class SumXCheck {

    public static void check(int x) {
        
        CProver.assume(x >= 0 && x <= 1000);        // preconditions

        int result = SumX.sum(x);

        int sum = x * (x + 1) / 2;

        boolean equal = false;

        if (result == sum){
            equal = true;
        }

        assert equal;
    }
}
