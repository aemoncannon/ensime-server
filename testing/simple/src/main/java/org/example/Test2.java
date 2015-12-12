package org.example;

public class Test2 {

    public static int compute() {
        int a = 2;
        int b = 3;
        return thing(a + b);
    }

    public static int thing(int a) {
        int b = 3;
        int c = a + b;
        return c;
    }

    static class Bar {
        public Bar() {}
    }
}
