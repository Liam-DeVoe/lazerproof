using System;

namespace BmTest
{
    public static class Program
    {
        public static int Main(string[] args)
        {
            switch (args[0])
            {
                case "probe": Probe.Run(); return 0;
                case "modinfo": ModInfo.Run(); return 0;
                case "letters": Probe.Letters(); return 0;
                case "whitespace": Probe.WhiteSpace(); return 0;
                case "sorttest": Probe.SortTest(int.Parse(args[1]), int.Parse(args[2])); return 0;
                case "dump": return Dumper.DumpOne(args[1], args.Length > 2 ? args[2] : null);
                case "batch": return Dumper.Batch(args[1], args[2]);
            }
            return 2;
        }
    }
}
