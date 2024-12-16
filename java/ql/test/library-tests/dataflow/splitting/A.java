public class A {
  static Object source(String tag) { return null; }

  static void sink(Object o) { }

  void test1(boolean b) {
    Object x;
    if (b) {
      x = source("A1");
    } else {
      x = source("B1");
    }
    Object y = x;
    if (!b) {
      sink(y); // $ hasValueFlow=B1
    }
  }

  void test2(boolean b) {
    Object x = null;
    if (b) {
      x = source("A2");
    }
    Object y = x;
    if (b) {
      sink(y); // $ hasValueFlow=A2
    } else {
      sink(y); // no flow
    }
  }

  void test3(boolean b) {
    Object x;
    if (b) {
      x = source("A3");
    } else {
      x = source("B3");
    }
    Object y = x;
    if (b) {
      sink(y); // $ hasValueFlow=A3 SPURIOUS: hasValueFlow=B3
    } else {
      sink(y); // $ hasValueFlow=B3 SPURIOUS: hasValueFlow=A3
    }
  }

  void loop1(boolean[] a) {
    Object x = null;
    for (int i = 0; i < a.length; i++) {
      boolean b = a[i];
      if (b) {
        x = source("Loop1");
      }
      if (!b) {
        sink(x); // $ hasValueFlow=Loop1
      }
      // flow can loop around from one iteration to the next
    }
  }

  void loop2(boolean[] a) {
    for (int i = 0; i < a.length; i++) {
      // x is local to the loop iteration and thus cannot loop around and reach the sink
      Object x = null;
      boolean b = a[i];
      if (b) {
        x = source("Loop2");
      }
      if (!b) {
        sink(x); // $ SPURIOUS: hasValueFlow=Loop2
      }
    }
  }
}
