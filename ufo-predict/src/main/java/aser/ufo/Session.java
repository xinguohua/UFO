package aser.ufo;

import aser.ufo.misc.*;
import aser.ufo.trace.EventLoader;
import aser.ufo.trace.Indexer;
import com.google.common.collect.Lists;
import config.Configuration;
import it.unimi.dsi.fastutil.ints.IntArrayList;
import it.unimi.dsi.fastutil.longs.Long2ObjectOpenHashMap;
import it.unimi.dsi.fastutil.longs.LongArrayList;
import it.unimi.dsi.fastutil.longs.LongListIterator;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import trace.AbstractNode;
import trace.DeallocNode;
import trace.MemAccNode;

import java.io.*;
import java.util.*;
import java.util.concurrent.*;

/**
 * one session for one execution
 */
public abstract class Session {

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

  public Session(Configuration c) throws Exception {
    config = c;
    exe = Executors.newFixedThreadPool(UFO.PAR_LEVEL);
    traceLoader = new EventLoader(exe, config.traceDir);
    solver = new SimpleSolver(config);
  }

  public void init() {

    addr2line = new Addr2line(traceLoader.getModuleList());
    windowSize = (int) config.window_size;
    if (windowSize < 10) {
      windowSize = (int) (UFO.MAX_MEM_SIZE * 0.9 / UFO.AVG_EVENT / traceLoader.fileInfoMap.size()
          // half mem for events, half for z3
          / 0.7);
      LOG.info("Suggested window size {}", windowSize);
    } 
//    else {
//      LOG.info("window size {}", windowSize);
//    }
    traceLoader.init(windowSize);

    try {
      writerB = new PrintWriter(new FileWriter("uaf_schedules.txt", true));// {
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



  protected void prepareConstraints(Indexer indexer) {
    solver.setReachEngine(indexer.getReachEngine());

    solver.declareVariables(indexer.getAllNodeSeq());
    // start < tid_first
    solver.buildSyncConstr(indexer);
  }





  public abstract void start();



  public void writeCallStack(Indexer indexer, AbstractNode node) {
	    long thisPC = Addr2line.getPC(node);

    LongArrayList callStack = indexer.buildCallStack(node);
    if (callStack == null || callStack.size() < 1)
      {
    	//JEFF
    	//if we did not record func entry and exit
    	AddrInfo ai = addr2line.getAddrInfoFromPC(thisPC);
    	if(ai!=null)
    	{
    	writerD.append("  ");
        writerD.append(ai.toString()).append('\n');
    	}
        return;
      };
    if (thisPC > 0) {
      callStack.push(thisPC);
    }
    Long2ObjectOpenHashMap<AddrInfo> srcInfo = addr2line.sourceInfo(callStack);
    int pad = 0;
    LongListIterator iter =  callStack.listIterator(callStack.size());
    while (iter.hasPrevious()) {
      int i = 0;
      long pc = iter.previousLong();
      AddrInfo ai = srcInfo.get(pc);
      if (ai == null)
        continue;
      while (i++ != pad)
        writerD.append("  ");
      writerD.append(ai.toString()).append(" pc: 0x"+Long.toHexString(ai.addr)).append('\n');//JEFF
      pad++;
    }
  }
}
