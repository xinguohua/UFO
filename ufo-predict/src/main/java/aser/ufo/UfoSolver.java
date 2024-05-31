package aser.ufo;

import aser.ufo.misc.Pair;
import aser.ufo.trace.Indexer;
import it.unimi.dsi.fastutil.ints.IntArrayList;
import it.unimi.dsi.fastutil.longs.LongArrayList;
import it.unimi.dsi.fastutil.shorts.Short2ObjectOpenHashMap;
import trace.AbstractNode;
import trace.DeallocNode;
import trace.MemAccNode;
import trace.ReadNode;

import java.util.ArrayList;

/**
 * Created by cbw on 11/15/16.
 */
public interface UfoSolver {


  void rebuildIntraThrConstr(Short2ObjectOpenHashMap<ArrayList<AbstractNode>> map, Pair<MemAccNode, MemAccNode> reorderPair);

  String buildReorderConstrOpt(ArrayList<ReadNode> allReadNodes, boolean influence);

  //  disable nLock engine
  void buildSyncConstr(Indexer index);

  void declareVariables(ArrayList<AbstractNode> trace);

  boolean canReach(AbstractNode node1, AbstractNode node2);

  void reset();
}
