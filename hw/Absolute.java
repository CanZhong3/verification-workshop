// 1. Write the contract of abs and verify it.
//   ./esc hw/Absolute.java
public class Absolute {

    // Returns the absolute value of n.
    //@ requires n != Integer.MIN_VALUE;
    public static int abs(int n) {
        if (n < 0) {
            return -n;
        }
        return n;
    }
}
