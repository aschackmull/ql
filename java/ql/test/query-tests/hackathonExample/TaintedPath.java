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

  public void sendUserFile(Socket sock, String user) throws IOException {
    BufferedReader filenameReader = new BufferedReader(new InputStreamReader(sock.getInputStream(), "UTF-8"));
    String filename = filenameReader.readLine();
    // BAD: read from a file without checking its path
    BufferedReader fileReader = new BufferedReader(new FileReader(filename));
    String fileLine = fileReader.readLine();
    while(fileLine != null) {
        sock.getOutputStream().write(fileLine.getBytes());
        fileLine = fileReader.readLine();
    }
  }
}
