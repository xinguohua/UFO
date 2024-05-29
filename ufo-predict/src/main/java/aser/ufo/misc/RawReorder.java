package aser.ufo.misc;

import it.unimi.dsi.fastutil.longs.LongArrayList;
import trace.DeallocNode;
import trace.MemAccNode;

import java.util.ArrayList;

public class RawReorder {
  final Pair<MemAccNode, MemAccNode> switchPair;

  final Pair<MemAccNode, MemAccNode> dependPair;

  public final ArrayList<String> schedule;

  public RawReorder(Pair<MemAccNode, MemAccNode> switchPair, Pair<MemAccNode, MemAccNode> dependPair, ArrayList<String> schedule) {
    this.switchPair = switchPair;
    this.dependPair = dependPair;
    this.schedule = schedule;
  }
}
