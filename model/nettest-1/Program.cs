static class Program {
  static int Main(string[] args) {
    if (args.Length > 0 && args[0] == "probe") { Probe.Run(); return 0; }
    if (args.Length > 1 && args[0] == "jit") { JitW.Run(args); return 0; }
    if (args.Length > 0 && args[0] == "lazer") return Gen.RunLazer(args);
    return Gen.Run(args);
  }
}
