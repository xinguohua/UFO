package aser.ufo;

import aser.ufo.misc.Addr2line;
import aser.ufo.misc.AddrInfo;
import aser.ufo.misc.Pair;
import aser.ufo.misc.RawReorder;
import aser.ufo.trace.AllocaPair;
import aser.ufo.trace.EventLoader;
import aser.ufo.trace.Indexer;
import aser.ufo.trace.TLEventSeq;
import config.Configuration;
import it.unimi.dsi.fastutil.ints.IntArrayList;
import it.unimi.dsi.fastutil.longs.Long2ObjectOpenHashMap;
import it.unimi.dsi.fastutil.longs.LongArrayList;
import it.unimi.dsi.fastutil.longs.LongListIterator;
import it.unimi.dsi.fastutil.shorts.Short2ObjectOpenHashMap;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import trace.AbstractNode;
import trace.DeallocNode;
import trace.MemAccNode;

import java.io.FileWriter;
import java.io.IOException;
import java.io.PrintWriter;
import java.util.*;
import java.util.concurrent.*;


public class Session {
    protected static final Logger LOG = LoggerFactory.getLogger(Session.class);

    public final Configuration config;
    public final EventLoader traceLoader;
    public final SimpleSolver solver;
    public Addr2line addr2line;
    public final ExecutorService exe;
    protected int windowSize;

    PrintWriter writerD;
    PrintWriter writerB;

    public Session(Configuration c) {
        config = c;
        exe = Executors.newFixedThreadPool(UFO.PAR_LEVEL);
        traceLoader = new EventLoader(exe, config.traceDir);
        solver = new SimpleSolver(config);
    }


    int loadedEventCount = 0;


    public void init() {

        addr2line = new Addr2line(traceLoader.getModuleList());
        windowSize = (int) config.window_size;
        if (windowSize < 10) {
            windowSize = (int) (UFO.MAX_MEM_SIZE * 0.9 / UFO.AVG_EVENT / traceLoader.fileInfoMap.size()
                    // half mem for events, half for z3
                    / 0.7);
            LOG.info("Suggested window size {}", windowSize);
        }
        traceLoader.init(windowSize);

        try {
            writerB = new PrintWriter(new FileWriter("uaf_schedules.txt", true));
            writerD = new PrintWriter(new FileWriter("uaf_list.txt", true)) {
                public PrintWriter append(CharSequence csq) {
                    super.append(csq);
                    writerB.append(csq);
                    System.out.append(csq);
                    return this;
                }

                public PrintWriter append(char c) {
                    super.write(c);
                    writerB.append(c);
                    System.out.append(c);
                    return this;
                }
            };
        } catch (IOException e) {
            LOG.error("could not create log file", e);
        }
    }

    public void start() {
        traceLoader.loadSycnTraceEvent();
        traceLoader.preprocessSycn();
        printTraceStats();
        while (traceLoader.hasNext()) {
            Indexer indexer = new Indexer();
            traceLoader.updateIndexerWithAliveThreads(indexer);

            //1. set the number of threads
            //2. assign index to each thread
            indexer.processNode();
            loadedEventCount += indexer.metaInfo.rawNodeCount;


            Map<Pair<MemAccNode, MemAccNode>, Pair<MemAccNode, MemAccNode>> reorderPairMap = indexer.getReorderPairMap();
            if (reorderPairMap == null || reorderPairMap.isEmpty()) return;

            prepareConstraints(indexer);

            solver.setCurrentIndexer(indexer);

            List<RawReorder> rawReorders = solveReorderConstr(indexer.getTSTid2sqeNodes(), indexer.getReorderPairMap().entrySet().iterator(), UFO.PAR_LEVEL);

            displayRawReorders(rawReorders, indexer, traceLoader);
        }
        exe.shutdownNow();
    }


    public static void displayRawReorders(List<RawReorder> rawReorders, Indexer indexer, EventLoader traceLoader) {
        PrintWriter writer = null;
        try {
            writer = new PrintWriter(new FileWriter("output.txt"));

            for (RawReorder rawReorder : rawReorders) {
                String header = "RawReorder:";
                System.out.println(header);
                writer.println(header);

                String switchPair = "  Switch Pair: " + rawReorder.switchPair;
                System.out.println(switchPair);
                writer.println(switchPair);

                String dependPair = "  Depend Pair: " + rawReorder.dependPair;
                System.out.println(dependPair);
                writer.println(dependPair);

                String scheduleHeader = "  Schedule:";
                System.out.println(scheduleHeader);
                writer.println(scheduleHeader);

                for (String s : rawReorder.schedule) {
                    String[] parts = s.split("-");
                    short tid = Short.parseShort(parts[1]);
                    String color = traceLoader.threadColorMap.get(tid);
                    AbstractNode node = indexer.getAllNodeMap().get(s);

                    String nodeString = node != null ? node.toString() : "[Node not found]";
                    String line = color + "    " + s + "    " + nodeString + "\u001B[0m";

                    System.out.println(line);  // Print colored line to console
                    writer.println(line);       // Write colored line to file
                }
                System.out.println();
                writer.println();
            }
        } catch (IOException e) {
            e.printStackTrace();
        } finally {
            if (writer != null) {
                writer.close();
            }
        }
    }



    public void printTraceStats() {
        System.out.println("Start Events: " + TLEventSeq.stat.c_tstart);
        System.out.println("Join Events: " + TLEventSeq.stat.c_join);
        System.out.println("Lock Events: " + TLEventSeq.stat.c_lock);
        System.out.println("Unlock Events: " + TLEventSeq.stat.c_unlock);
        System.out.println("Wait/Notify Events: " + TLEventSeq.stat.c_isync);

        long totalsync = TLEventSeq.stat.c_tstart + TLEventSeq.stat.c_join + TLEventSeq.stat.c_lock + TLEventSeq.stat.c_unlock + TLEventSeq.stat.c_isync;

        System.out.println("Alloc Events: " + TLEventSeq.stat.c_alloc);
        System.out.println("DeAlloc Events: " + TLEventSeq.stat.c_dealloc);

        //total reads
        long reads = TLEventSeq.stat.c_read[0];
        for (int i = 1; i < 4; i++)
            reads += TLEventSeq.stat.c_read[i];

        //total writes
        long writes = TLEventSeq.stat.c_write[0];
        for (int i = 1; i < 4; i++)
            writes += TLEventSeq.stat.c_write[i];

        long toreads = reads + TLEventSeq.stat.c_range_r;
        long towrites = writes + TLEventSeq.stat.c_range_w;


        System.out.println("Total Sync Events: " + totalsync);
        System.out.println("Total Alloc Events: " + TLEventSeq.stat.c_alloc);
        System.out.println("Total USE Events: " + (toreads + towrites));
        System.out.println("Total Free Events: " + TLEventSeq.stat.c_dealloc);
        System.out.println("Total Read Events: " + toreads);
        System.out.println("Total Write Events: " + towrites);
        System.out.println("Total Events: " + TLEventSeq.stat.c_total);
    }


    public List<RawReorder> solveReorderConstr(final Short2ObjectOpenHashMap<ArrayList<AbstractNode>> map, Iterator<Map.Entry<Pair<MemAccNode, MemAccNode>, Pair<MemAccNode, MemAccNode>>> iter, int limit) {

        CompletionService<RawReorder> cexe = new ExecutorCompletionService<RawReorder>(exe);
        int task = 0;
        while (iter.hasNext() && limit > 0) {
            limit--;
            Map.Entry<Pair<MemAccNode, MemAccNode>, Pair<MemAccNode, MemAccNode>> e = iter.next();
            final Pair<MemAccNode, MemAccNode> switchPair = e.getKey();
            final Pair<MemAccNode, MemAccNode> dependPair = e.getValue();

            cexe.submit(new Callable<RawReorder>() {
                @Override
                public RawReorder call() throws Exception {
                    ArrayList<String> bugSchedule = solver.searchReorderSchedule(map, switchPair, dependPair);
                    if (bugSchedule != null) return new RawReorder(switchPair, dependPair, bugSchedule);
                    else return null;

                }
            });
            task++;
        }

        ArrayList<RawReorder> ls = new ArrayList<RawReorder>(task);
        try {
            while (task-- > 0) {
                Future<RawReorder> f = cexe.take(); //blocks if none available
                RawReorder rawReorder = f.get();
                if (rawReorder != null) ls.add(rawReorder);
            }
        } catch (Exception e) {
            throw new RuntimeException(e);
        }
        return ls;
    }


    public void writeCallStack(Indexer indexer, AbstractNode node) {
        long thisPC = Addr2line.getPC(node);

        LongArrayList callStack = indexer.buildCallStack(node);
        if (callStack == null || callStack.isEmpty()) {
            //JEFF
            //if we did not record func entry and exit
            AddrInfo ai = addr2line.getAddrInfoFromPC(thisPC);
            if (ai != null) {
                writerD.append("  ");
                writerD.append(ai.toString()).append('\n');
            }
            return;
        }
        ;
        if (thisPC > 0) {
            callStack.push(thisPC);
        }
        Long2ObjectOpenHashMap<AddrInfo> srcInfo = addr2line.sourceInfo(callStack);
        int pad = 0;
        LongListIterator iter = callStack.listIterator(callStack.size());
        while (iter.hasPrevious()) {
            int i = 0;
            long pc = iter.previousLong();
            AddrInfo ai = srcInfo.get(pc);
            if (ai == null) continue;
            while (i++ != pad) writerD.append("  ");
            writerD.append(ai.toString()).append(" pc: 0x").append(Long.toHexString(ai.addr)).append('\n');//JEFF
            pad++;
        }
    }

    protected void prepareConstraints(Indexer indexer) {
        solver.setReachEngine(indexer.getReachEngine());

        solver.declareVariables(indexer.getAllNodeSeq());
        // start < tid_first
        solver.buildSyncConstr(indexer);
    }

}
