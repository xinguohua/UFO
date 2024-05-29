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
    //  public final UfoSolver solver2;
    public Addr2line addr2line;
    public final ExecutorService exe;
    protected int windowSize;

    PrintWriter writerD;
    PrintWriter writerB;

    int sessionID;
    int uafID;

    public Session(Configuration c) {
        config = c;
        exe = Executors.newFixedThreadPool(UFO.PAR_LEVEL);
        traceLoader = new EventLoader(exe, config.traceDir);
        solver = new SimpleSolver(config);
    }

    int __c1 = 0;
    int __c2 = 0;
    int __c3 = 0;

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
        traceLoader.preprocessWaitNotify();//JEFF
        printTraceStats();//JEFF

        sessionID = 0;
        uafID = 0;

        while (traceLoader.hasNext()) {
            sessionID++;
            Indexer indexer = new Indexer();
            traceLoader.populateIndexer(indexer);

            loadedEventCount += indexer.metaInfo.rawNodeCount;


            //ADD THREAD FORK-JOIN ORDER TO PRUNE AWAY OBVIOUS CASES

            HashMap<MemAccNode, HashSet<AllocaPair>> candidateUafLs = indexer.getMachtedAcc();

//      if(candidateUafLs.isEmpty())continue;

            if (config.fast_detect) {
                LOG.info("candidateUafLs: {}", candidateUafLs.size());
                Iterator<Map.Entry<MemAccNode, HashSet<AllocaPair>>> iter1 = candidateUafLs.entrySet().iterator();
                while (iter1.hasNext()) {

                    Map.Entry<MemAccNode, HashSet<AllocaPair>> e = iter1.next();
                    final MemAccNode acc = e.getKey();
                    final HashSet<AllocaPair> pairs = e.getValue();

                    writerD.append("\r\n------- #" + acc.tid + " use call stack  \r\n");
                    writeCallStack(indexer, acc);

                    for (AllocaPair pair : pairs) {
                        DeallocNode free = pair.deallocNode;
                        writerD.append("\r\n------- #" + free.tid + " free call stack  \r\n");
                        writeCallStack(indexer, free);
                    }
                }


                __c3 += candidateUafLs.size();
                //      5485

                //     System.out.println("candidateUafLs.size()  " + candidateUafLs.size() + "    " + __c3);

                //      if (System.currentTimeMillis() > 1) {
                //        System.out.println(" continue;");
                //        continue;
                //      }

                __c1 += indexer.metaInfo.sharedAddrs.size();
                for (HashSet<AllocaPair> sp : candidateUafLs.values()) {
                    if (sp.size() > 1) __c2++;
                }


            } else {
                prepareConstraints(indexer);

                solver.setCurrentIndexer(indexer);

                ct_candidataUaF.add(candidateUafLs.size());

                writerD.append("#" + sessionID + " Session").append("   candidateUafLs: " + candidateUafLs.size()).append('\n');


//      Iterator<Map.Entry<MemAccNode, HashSet<AllocaPair>>> iter = candidateUafLs.entrySet().iterator();
//      while (iter.hasNext()) {
//        List<RawUaf> ls = solveUafConstr(iter, UFO.PAR_LEVEL);
//        if (ls != null && ls.size() > 0)
//          outputUafLs(ls, indexer);
//      }

                List<RawReorder> ls = solveReorderConstr(indexer.getTSTid2sqeNodes(), indexer.getReorderPairMap().entrySet().iterator(), UFO.PAR_LEVEL);
                if (ls != null && ls.size() > 0)
//          outputUafLs(ls, indexer);


                    if (solver.ct_constr.size() > 0) {
                        ct_vals.push(solver.ct_vals);
                        Pair<Integer, Long> max_total = _Max_total(solver.ct_constr);
                        ct_constr.push(max_total.value.intValue());
                        if (max_total.value > Integer.MAX_VALUE)
                            throw new RuntimeException("Overflow long -> int " + max_total.value);
                        ct_max_constr.push(max_total.key);
//        int avg = _Max_total.value / solver.ct_constr.size();
//        ct_constr_max_avg.add(new Pair<Integer, Integer>(_Max_total.key, avg));
                    }
                solver.reset(); // release constraints for this round
                writerD.append("\r\n");
            } // while


        }
//    System.out.println(__c1 + "   " + __c2 + "   " + __c3);
//    System.out.println(config.window_size +  "  Time:  " + ((System.currentTimeMillis() - _t1) / 1000));
        _PrintStat();
        exe.shutdown();
        try {
            writerD.close();
            exe.awaitTermination(10, TimeUnit.SECONDS);
        } catch (Exception e) {
            LOG.error(" error finishing ", e);
        }
        exe.shutdownNow();
    }


    public HashMap<Integer, Integer> ct_uaf = new HashMap<Integer, Integer>();
    public IntArrayList ct_vals = new IntArrayList(1000);
    public IntArrayList ct_constr = new IntArrayList(1000);
    public IntArrayList ct_max_constr = new IntArrayList(1000);
    public IntArrayList ct_candidataUaF = new IntArrayList(1000);
//  public ArrayList<Pair<Integer, Integer>> ct_constr_max_avg = new ArrayList<Pair<Integer, Integer>>(100);


    public static Pair<Integer, Long> _Max_total(IntArrayList ct_constr) {
        long c = 0;
        int max = 0;
        for (int i : ct_constr) {
            c += i;
            if (i > max) max = i;
        }
        return new Pair<Integer, Long>(max, c);
    }

    public static int _Avg(IntArrayList ct_constr) {
        if (ct_constr == null || ct_constr.size() == 0) return -1;
        long c = 0;
        for (int i : ct_constr)
            c += i;

        return (int) (c / ct_constr.size());
    }


    public void _PrintStat() {
        int max_max = _Max_total(ct_max_constr).key;
        Pair<Integer, Long> mc_constr = _Max_total(ct_constr);

        System.out.println("\r\n=================================\r\n");
        System.out.printf("Session %d | avg vals %d | constr max %d  avg %d | total constr %d | total candidate UaF %d \r\n", sessionID, _Avg(ct_vals), max_max, _Avg(ct_constr), mc_constr.value, _Max_total(ct_candidataUaF).value);

        System.out.println("Solved UAF: " + ct_uaf);


        //printTraceStats();


//    public long c_tstart = 0;
//    public long c_join = 0;
//    public long c_lock = 0;
//    public long c_unlock = 0;
//    public long c_alloc = 0;
//    public long c_dealloc = 0;
//    public long[] c_read = new long[4];
//    public long[] c_write = new long[4];
//    public long c_range_w = 0;
//    public long c_range_r = 0;
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

//    System.out.println("Read Events: " + reads);
//    System.out.println("Write Events: " + writes);
//    System.out.println("RRead Events: " + TLEventSeq.stat.c_range_r);
//    System.out.println("RWrite Events: " + TLEventSeq.stat.c_range_w);

        long toreads = reads + TLEventSeq.stat.c_range_r;
        long towrites = writes + TLEventSeq.stat.c_range_w;

        //long total = totalsync+TLEventSeq.stat.c_alloc+TLEventSeq.stat.c_dealloc+toreads+towrites;

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
        if (callStack == null || callStack.size() < 1) {
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
            writerD.append(ai.toString()).append(" pc: 0x" + Long.toHexString(ai.addr)).append('\n');//JEFF
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
