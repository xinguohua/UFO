package aser.ufo;

import aser.ufo.misc.Pair;
import aser.ufo.misc.RawReorder;
import aser.ufo.misc.RawUaFCpx;
import aser.ufo.misc.RawUaf;
import aser.ufo.trace.AllocaPair;
import aser.ufo.trace.Indexer;
import aser.ufo.trace.TLEventSeq;
import config.Configuration;
import it.unimi.dsi.fastutil.ints.IntArrayList;
import it.unimi.dsi.fastutil.shorts.Short2ObjectOpenHashMap;
import trace.AbstractNode;
import trace.DeallocNode;
import trace.MemAccNode;

import java.util.*;
import java.util.concurrent.*;


public class Session2 extends Session {

  public Session2(Configuration c) throws Exception {
    super(c);
    
  }

  int __c1 = 0;
  int __c2 = 0;
  int __c3 = 0;

  int loadedEventCount = 0;

  

  
  @Override
  public void start() {
	 traceLoader.preprocessWaitNotify();//JEFF
	  printTraceStats();//JEFF
	  
    sessionID = 0;
    long _t1 = System.currentTimeMillis();
    uafID = 0;

    while (traceLoader.hasNext()) {
      sessionID++;
      Indexer indexer = new Indexer();
      traceLoader.populateIndexer(indexer);

      loadedEventCount += indexer.metaInfo.rawNodeCount;

      
      //ADD THREAD FORK-JOIN ORDER TO PRUNE AWAY OBVIOUS CASES
      
      HashMap<MemAccNode, HashSet<AllocaPair>> candidateUafLs = indexer.getMachtedAcc();

//      if(candidateUafLs.isEmpty())continue;
      
      if (config.fast_detect)
      {
	      LOG.info("candidateUafLs: {}", candidateUafLs.size());
	      Iterator<Map.Entry<MemAccNode, HashSet<AllocaPair>>> iter1 = candidateUafLs.entrySet().iterator();
	      while (iter1.hasNext()) {
	    	  
	    	  Map.Entry<MemAccNode, HashSet<AllocaPair>> e = iter1.next();
	          final MemAccNode acc = e.getKey();
	          final HashSet<AllocaPair> pairs = e.getValue();
	          
	      writerD.append("\r\n------- #"+acc.tid+" use call stack  \r\n");
	      writeCallStack(indexer, acc);
	
		     for(AllocaPair pair: pairs)
		     {
		    	 DeallocNode free = pair.deallocNode;
		        writerD.append("\r\n------- #"+free.tid+" free call stack  \r\n");
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
	        if (sp.size() > 1)
	          __c2++;
	      }

      
        
      }
      else
	      {
      prepareConstraints(indexer);
      
      solver.setCurrentIndexer(indexer);

      ct_candidataUaF.add(candidateUafLs.size());

      writerD.append("#" + sessionID + " Session")
          .append("   candidateUafLs: " + candidateUafLs.size()).append('\n');


//      Iterator<Map.Entry<MemAccNode, HashSet<AllocaPair>>> iter = candidateUafLs.entrySet().iterator();
//      while (iter.hasNext()) {
//        List<RawUaf> ls = solveUafConstr(iter, UFO.PAR_LEVEL);
//        if (ls != null && ls.size() > 0)
//          outputUafLs(ls, indexer);
//      }

        List<RawReorder> ls = solveReorderConstr(indexer.getTSTid2sqeNodes(),indexer.getReorderPairMap().entrySet().iterator(), UFO.PAR_LEVEL);
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



private HashSet<Pair<Long, Long>> knownUAF = new HashSet<Pair<Long, Long>>(250);

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
      if (i > max)
        max = i;
    }
    return new Pair<Integer, Long>(max, c);
  }
  public static int _Avg(IntArrayList ct_constr) {
    if (ct_constr == null || ct_constr.size() == 0)
      return -1;
    long c = 0;
    for (int i : ct_constr)
      c += i;

    return (int) (c /  ct_constr.size());
  }

  
  public void _PrintStat() {
    int max_max = _Max_total(ct_max_constr).key;
    Pair<Integer, Long> mc_constr = _Max_total(ct_constr);

    System.out.println("\r\n=================================\r\n");
    System.out.printf(
        "Session %d | avg vals %d | constr max %d  avg %d | total constr %d | total candidate UaF %d \r\n",
        sessionID,
        _Avg(ct_vals),
        max_max,
        _Avg(ct_constr),
        mc_constr.value,
        _Max_total(ct_candidataUaF).value
        );

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

    long totalsync = TLEventSeq.stat.c_tstart+TLEventSeq.stat.c_join+TLEventSeq.stat.c_lock+TLEventSeq.stat.c_unlock+TLEventSeq.stat.c_isync;
    
    System.out.println("Alloc Events: " + TLEventSeq.stat.c_alloc);
    System.out.println("DeAlloc Events: " + TLEventSeq.stat.c_dealloc);
    
    //total reads 
    long reads = TLEventSeq.stat.c_read[0];
    for(int i=1;i<4;i++)
    	reads+=TLEventSeq.stat.c_read[i];
    
    //total writes 
    long writes = TLEventSeq.stat.c_write[0];
    for(int i=1;i<4;i++)
    	writes+=TLEventSeq.stat.c_write[i];
    
//    System.out.println("Read Events: " + reads);
//    System.out.println("Write Events: " + writes);
//    System.out.println("RRead Events: " + TLEventSeq.stat.c_range_r);
//    System.out.println("RWrite Events: " + TLEventSeq.stat.c_range_w);
    
    long toreads = reads+TLEventSeq.stat.c_range_r;
    long towrites = writes+TLEventSeq.stat.c_range_w;

    //long total = totalsync+TLEventSeq.stat.c_alloc+TLEventSeq.stat.c_dealloc+toreads+towrites;
    
    System.out.println("Total Sync Events: " + totalsync);
    System.out.println("Total Alloc Events: " + TLEventSeq.stat.c_alloc);
    System.out.println("Total USE Events: " + (toreads+towrites));
    System.out.println("Total Free Events: " + TLEventSeq.stat.c_dealloc);
    System.out.println("Total Read Events: " + toreads);
    System.out.println("Total Write Events: " + towrites);
    System.out.println("Total Events: " + TLEventSeq.stat.c_total);
}

  @Override
  public void outputUafLs(List<RawUaf> uafLs, Indexer indexer) {
    LOG.info("Use-After-Free bugs: {}", uafLs.size());
    for (RawUaf uaf : uafLs) {
      long dePC;
      if (uaf instanceof RawUaFCpx) {
        RawUaFCpx cu = (RawUaFCpx) uaf;
        dePC = cu.pairs.hashCode();
      } else {
         dePC = uaf.deallocNode.pc;
      }
      Pair<Long, Long> pair = new Pair<Long, Long>(dePC, uaf.accNode.pc);
      if (knownUAF.contains(pair)) {
        //System.out.println("Skip known access violation  ");
        continue;
      }
      knownUAF.add(pair);
      uafID++;

      writerD.append("#" + uafID + "  UAF").append("\r\n");
      if (uaf instanceof RawUaFCpx) {
        writerD.append("\r\n\r\n!!!!!!!!! Real UaF   " + ((RawUaFCpx)uaf).pairs.size() + "\r\n");
        System.out.println("\r\n\r\n!!!!!!!!! Real UaF   " + ((RawUaFCpx)uaf).pairs.size() + "\r\n");
      }

      
      writerD.append("\r\n------- #"+uaf.accNode.tid+" use call stack  \r\n");
      writeCallStack(indexer, uaf.accNode);

      int sz = 1;
      if (uaf instanceof RawUaFCpx) {
        RawUaFCpx cu = (RawUaFCpx) uaf;
        sz = cu.pairs.size();
        for (AllocaPair ap : cu.pairs) {
          if (ap.deallocNode != null) {
          writerD.append("\r\n------- #"+uaf.deallocNode.tid+" free call stack  \r\n");
          writeCallStack(indexer, ap.deallocNode);
          }
        }
      } else {
        writerD.append("\r\n------- #"+uaf.deallocNode.tid+" free call stack  \r\n");
        writeCallStack(indexer, uaf.deallocNode);
      }

      if (ct_uaf.containsKey(sz)) {
        ct_uaf.put(sz, ct_uaf.get(sz) + 1);
      } else ct_uaf.put(sz, 1);
    }
  }

  protected void _stat(HashMap<MemAccNode, HashSet<AllocaPair>> candidateUafLs) {
    HashMap<Integer, Integer> ct = new HashMap<Integer, Integer>();
    int cm = 0;
    for (HashSet<AllocaPair> p : candidateUafLs.values()) {
      int sz = p.size();
      if (sz > 1)
        cm++;
      if (ct.containsKey(sz))
        ct.put(sz, ct.get(sz) + 1);
      else ct.put(sz, 1);
    }
    System.out.println(((float)cm / candidateUafLs.size()) + "    " + ct);
  }





  public List<RawReorder> solveReorderConstr(final Short2ObjectOpenHashMap<ArrayList<AbstractNode>> map, Iterator<Map.Entry<Pair<MemAccNode, MemAccNode>, Pair<MemAccNode, MemAccNode>>>  iter, int limit) {

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
        if (rawReorder != null)
          ls.add(rawReorder);
      }
    } catch (Exception e) {
      throw new RuntimeException(e);
    }
    return ls;
  }

}
