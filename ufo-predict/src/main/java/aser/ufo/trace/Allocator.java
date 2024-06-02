package aser.ufo.trace;

import aser.ufo.NewReachEngine;
import aser.ufo.Reorder;
import it.unimi.dsi.fastutil.longs.Long2ObjectRBTreeMap;
import it.unimi.dsi.fastutil.objects.ObjectCollection;
import it.unimi.dsi.fastutil.shorts.Short2ObjectMap;
import it.unimi.dsi.fastutil.shorts.Short2ObjectOpenHashMap;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import trace.AllocNode;
import trace.DeallocNode;
import trace.MemAccNode;

import java.util.*;

class TLAllocQ {
  //  Long2ObjectRBTreeMap
  ArrayList<AllocaPair> allocQ = new ArrayList<AllocaPair>(Reorder.INITSZ_S);

  Long2ObjectRBTreeMap<ArrayList<AllocaPair>> tree = new Long2ObjectRBTreeMap<ArrayList<AllocaPair>>(
      // addr in this tree follows DESC order
      // to map acc with tail map
      new Comparator<Long>() {
        @Override
        public int compare(Long x, Long y) {
          return (y < x) ? -1 : ((x.longValue() == y.longValue()) ? 0 : 1);
        }
      });

  public void add(AllocaPair g) {
    allocQ.add(g);
    final long addr = g.allocNode.addr;
    ArrayList<AllocaPair> ls = tree.get(addr);
    if (ls == null) {
      ls = new ArrayList<AllocaPair>(30);
      tree.put(addr, ls);
    }
    ls.add(g);
  }

}
/**
 * Created by cbw on 12/12/16.
 */
public class Allocator {

  private static final Logger LOG = LoggerFactory.getLogger(Allocator.class);

  private Short2ObjectOpenHashMap<TLAllocQ>
      tid2AllocQ = new Short2ObjectOpenHashMap<TLAllocQ>(Reorder.INITSZ_S / 2);

  private HashSet<DeallocNode> unmatched = new HashSet<DeallocNode>(Reorder.INITSZ_S);
  HashMap<MemAccNode, HashSet<AllocaPair>> machtedAcc = new HashMap<MemAccNode, HashSet<AllocaPair>>(Reorder.INITSZ_S * 2);

  private long count_alloc = 0;
  private long count_dealloc = 0;
  public void push(AllocNode allocNode) {
    count_alloc++;
    short tid = allocNode.tid;
    TLAllocQ q = tid2AllocQ.get(tid);
    if (q == null) {
      q = new TLAllocQ();
      tid2AllocQ.put(tid, q);
    }
    AllocaPair g = new AllocaPair(allocNode);
    q.add(g);
  }

  public void insert(DeallocNode deallocNode) {
    count_dealloc++;
    short tid = deallocNode.tid;
    TLAllocQ q = tid2AllocQ.get(tid);
    if (q != null) {
      ListIterator<AllocaPair> iter = q.allocQ.listIterator(q.allocQ.size());
      while (iter.hasPrevious()) {
        AllocaPair g = iter.previous();
        if (g.allocNode.addr == deallocNode.addr) {

          if (g.deallocNode == null) {
            deallocNode.length = g.allocNode.length;
            g.deallocNode = deallocNode;
          } else if (Indexer.CHECK_MEM_ERROR) {
            LOG.error("possible double free at {}, first free {}, second free {}", g.allocNode, g.allocNode, deallocNode);
            unmatched.add(deallocNode);
//            __df_nodes.add(deallocNode);
          }
          return;
        }
      }
    }
    //if we get here, probably the alloc is in a previous window or it is missed
    	
    unmatched.add(deallocNode);
  }


  public boolean checkAcc(MemAccNode accNode, NewReachEngine reachEngine) {

    HashSet<AllocaPair> matchedGrp = new HashSet<AllocaPair>(32);
    final long accAddr = accNode.getAddr();
    final short accTid = accNode.tid;
    for (Short2ObjectMap.Entry<TLAllocQ> e : tid2AllocQ.short2ObjectEntrySet()) {

      TLAllocQ q = e.getValue();
      ObjectCollection<ArrayList<AllocaPair>> lss = q.tree.tailMap(accAddr).values();
      for (ArrayList<AllocaPair> ls : lss)
        for (AllocaPair p : ls) {
          DeallocNode dn = p.deallocNode;
          if (dn == null
        		  //|| dn.tid == accTid//JEFF
        		  )
            continue;
          //AllocNode an = p.allocNode;//JEFF change to free node
          if (dn.addr <= accAddr&& 
              accAddr < dn.addr + dn.length
              && (dn.tid != accTid)//JEFF test  || accNode.idx>dn.idx
              && !reachEngine.canReach(accNode, dn)
              )

            matchedGrp.add(p);

        }
      // tail map
    } // tid
    if (matchedGrp.size() > 0) {
      machtedAcc.put(accNode, matchedGrp);
      return true;
    } else return false;
  }

  public int _storedAlloc() {
    int count = 0;
    for (Short2ObjectMap.Entry<TLAllocQ> e : tid2AllocQ.short2ObjectEntrySet()) {
      for (AllocaPair g : e.getValue().allocQ) {
        if (g.allocNode != null)
          count++;
      }
    }
    return count;
  }

  public List<Integer> _matchedAlloc() {
    int count1 = 0;
    int count2 = 0;
    int count3 = 0;
    for (Short2ObjectMap.Entry<TLAllocQ> e : tid2AllocQ.short2ObjectEntrySet()) {
      for (AllocaPair g : e.getValue().allocQ) {
        if (g.deallocNode != null) {
          count1++;
          if (g.deallocNode.tid == g.allocNode.tid)
            count2++;
        } else if (g.possibleDealloc != null && g.possibleDealloc.size() > 0) {
          count3++;
        }
      }
    }

    return Arrays.asList(count1, count2, count3);
  }


}



























