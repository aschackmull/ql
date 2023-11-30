package my.qltest;

import java.io.*;
import java.net.*;
import java.util.*;

public class TaintedPath {
  void test(InetAddress address) throws IOException {
    String taint = address.getHostName();
    List<String> l = new ArrayList<>();
    l.add(taint);
    sink1(l.get(0));
    String maybeTainted = doStuff(taint);
    sink2(maybeTainted);
  }

  void sink1(String s) {
    File file = new File(s);
  }

  String doStuff(String s) {
    return ""; // dummy code
  }

  void sink2(String s) {
    File file = new File(s);
  }
}
