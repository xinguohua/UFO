package aser.ufo.trace;

import aser.ufo.NewReachEngine;
import aser.ufo.Reorder;
import aser.ufo.misc.CModuleSection;
import aser.ufo.misc.CModuleList;
import it.unimi.dsi.fastutil.shorts.Short2ObjectRBTreeMap;
import it.unimi.dsi.fastutil.shorts.ShortOpenHashSet;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import trace.*;

import java.io.*;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Map;
import java.util.concurrent.ExecutorService;

public class EventLoader {

    private static final Logger LOG = LoggerFactory.getLogger(EventLoader.class);

    private static final String[] COLORS = {
            "\u001B[31m", // Red
            "\u001B[32m", // Green
            "\u001B[33m", // Yellow
            "\u001B[34m", // Blue
            "\u001B[35m", // Magenta
            "\u001B[36m", // Cyan
            "\u001B[37m"  // White
    };

    public Map<Short, String> threadColorMap = new HashMap<Short, String>();

    Map<Short, TLEventSeq> fileSeqinfo = new HashMap<>();



    public final ExecutorService exe;
    public final String folderName;
    public final Short2ObjectRBTreeMap<FileInfo> fileInfoMap;
    private final ShortOpenHashSet aliveTids = new ShortOpenHashSet(80);
    private int totalNumOfThreads;
    private ShortOpenHashSet allThreads = new ShortOpenHashSet(80);
    ;

    // total size
    private int windowSize;
    //  public static final short MAIN_TID = 0;
    public final CModuleList moduleList = new CModuleList();

    public EventLoader(ExecutorService exe, String folderName) {
        this.exe = exe;
        this.folderName = folderName;
        fileInfoMap = new Short2ObjectRBTreeMap<FileInfo>();
    }

    public void init(int wsz) {

        windowSize = wsz;

        final File dir = new File(folderName);
        File[] traces = dir.listFiles(new FileFilter() {
            public boolean accept(File f) {
                if (!f.canRead()) {
                    throw new IllegalArgumentException("Could not read file " + f + "  at " + dir);
                }
                return f.isFile();
            }
        });
        if (traces == null) throw new RuntimeException("Could not find folder " + folderName);
        if (traces.length == 0) throw new IllegalArgumentException("No trace file found at " + folderName);
//    int flimt = 2;


        for (File f : traces) {
            if (Reorder.MODULE_TXT.equals(f.getName())) {
                loadCModuleInfo(f);
                continue;
            } else if (Reorder.STAT_TXT.equals(f.getName())) {
                continue;
            } else if (Reorder.STAT_CSV.equals(f.getName())) {
                continue;
            }
            short tid = Short.parseShort(f.getName());
            long sz = f.length();
            FileInfo fi = new FileInfo(f, sz, tid);
            fileInfoMap.put(tid, fi);
            threadColorMap.put(tid,  COLORS[tid% COLORS.length]);
            allThreads.add(tid);
        }
        totalNumOfThreads = allThreads.size();

        if (moduleList.size() < 1) LOG.error("Empty module info " + moduleList);


        short mainTid = fileInfoMap.firstShortKey();
        aliveTids.add(mainTid);
        fileInfoMap.get(mainTid).enabled = true;
    }

//  protected AtomicInteger gidGen = new AtomicInteger(1);

    public int validCount() {
        return fileSeqinfo.size();
    }

    public boolean hasNext() {
        return validCount() > 0;
    }


    void loadCModuleInfo(File f) {
        BufferedReader reader = null;
        boolean mainExeLoaded = false;
        try {
            reader = new BufferedReader(new FileReader(f));
            String line = reader.readLine();
            while (null != line) {
                String[] infoLs = line.split("\\|");
//        if (infoLs.length < 8)
//          break;
                //if ((infoLs.length - 2 ) % 3 != 0) throw new IllegalArgumentException("module info format error " + f);
                int idx = 0;
                String moduleFullName = infoLs[idx++]; // name with path

                try {
                    // TODO: check to make sure switch from parseLong to parseUnsignedLong didn't break existing code ANDREW
                    long base = java.lang.Long.parseUnsignedLong(infoLs[idx++].trim(), 16);
                    //JEFF
                    long max = java.lang.Long.parseUnsignedLong(infoLs[idx++].trim(), 16);

                    if (max > base) {
                        CModuleSection m = new CModuleSection(moduleFullName, base, max);
                        moduleList.add(m);
                    }
                } catch (Exception e) {
                    e.printStackTrace();
                }

//        while (idx < infoLs.length) {
//          boolean _isExe = Integer.parseInt(infoLs[idx++].trim()) > 0;
//          long _begin = java.lang.Long.parseLong(infoLs[idx++].trim(), 16);
//          long _end = java.lang.Long.parseLong(infoLs[idx++].trim(), 16);
//
//          CModuleSection m = new CModuleSection(moduleFullName, base, _isExe, _begin, _end);
//
//          if (!mainExeLoaded) {
//            moduleList.addMainExe(m);
//            mainExeLoaded = true;
//          }
//          moduleList.add(m);
//        }
                line = reader.readLine();
            }
            reader.close();
        } catch (Exception e) {
            throw new RuntimeException(e);
        } finally {
            if (reader != null) try {
                reader.close();
            } catch (Throwable ex) {
                ex.printStackTrace();
            }
        }
    }

    public void updateIndexerWithAliveThreads(Indexer mIdx) {
        int tidCount = aliveTids.size();
        ShortOpenHashSet currentTids = new ShortOpenHashSet(aliveTids);
        final int ptLimit = windowSize;

        HashSet<Short> visited = new HashSet<>();
        while (!currentTids.isEmpty()) {
            ShortOpenHashSet nextTids = addTLSeq1(mIdx, currentTids, visited);
            tidCount += nextTids.size();
            updateAliveTids(nextTids);
            currentTids = nextTids;
        }

        removeVisitSeq(visited);
        mIdx.metaInfo.tidCount = tidCount;
    }




    private ShortOpenHashSet addTLSeq1(Indexer mIdx, ShortOpenHashSet tids, HashSet<Short> visited) {
        ShortOpenHashSet newTids = new ShortOpenHashSet(3);
        for (short tid : tids) {
            TLEventSeq seq1 = fileSeqinfo.get(tid);
            if (seq1.events != null && !seq1.events.isEmpty()) {
                visited.add(seq1.tid);
                mIdx.addTidSeq(seq1.tid, seq1.events);
            }
            if (seq1.newTids.isEmpty()) continue;
            newTids.addAll(seq1.newTids);
        } // for
        return newTids;
    }




    private void updateAliveTids(ShortOpenHashSet newTids) {
        newTids.removeAll(aliveTids);
        aliveTids.addAll(newTids);
    }

    private void removeEOFTraceFiles() {
        Iterator<Map.Entry<Short, FileInfo>> iter = fileInfoMap.entrySet().iterator();
        while (iter.hasNext()) {
            Map.Entry<Short, FileInfo> e = iter.next();
            FileInfo info = e.getValue();
            if (info.fileOffset >= info.fsize - 5) {
                iter.remove();
            }
        }
    }

    private void removeVisitSeq(HashSet<Short> visited) {
        fileSeqinfo.entrySet().removeIf(shortTLEventSeqEntry -> visited.contains(shortTLEventSeqEntry.getKey()));
    }

    public CModuleList getModuleList() {
        return moduleList;
    }


    public void loadAllEvent() {
        for (short tid : allThreads) {
            FileInfo fi = fileInfoMap.get(tid);
            if (fi != null) {
                TLEventSeq seq = new NewLoadingTask(fi).loadAllEvent();
                LOG.info("tid: " + tid + " Total Events:  " + seq.numOfEvents);
                fileSeqinfo.put(tid, seq);
                //reset file info so that it can be reused again
                fi.fileOffset = 0;
                fi.lastFileOffset = 0;
            }
        }
        System.out.println(fileSeqinfo);
    }

    public void processSycn() {
        for (short tid : allThreads) {
            TLEventSeq tlEventSeq = fileSeqinfo.get(tid);
            if (tlEventSeq != null && tlEventSeq.events != null) {
                for (AbstractNode node : tlEventSeq.events) {
                    if (node != null) {
                        if (node instanceof TBeginNode) {
                            NewReachEngine.saveToThreadFirstNode(tid, (TBeginNode) node);
                        } else if (node instanceof TEndNode) {
                            NewReachEngine.saveToThreadLastNode(tid, (TEndNode) node);
                        } else if (node instanceof TStartNode) {
                            NewReachEngine.saveToStartNodeList((TStartNode) node);
                        } else if (node instanceof TJoinNode) {
                            NewReachEngine.saveToJoinNodeList((TJoinNode) node);
                        } else if (node instanceof WaitNode) {
                            TLEventSeq.stat.c_isync++;
                            NewReachEngine.saveToWaitNotifyList((IWaitNotifyNode) node);
                        } else if (node instanceof NotifyNode) {
                            TLEventSeq.stat.c_isync++;
                            NewReachEngine.saveToWaitNotifyList((IWaitNotifyNode) node);
                        } else if (node instanceof NotifyAllNode) {
                            TLEventSeq.stat.c_isync++;
                            NewReachEngine.saveToWaitNotifyList((IWaitNotifyNode) node);
                        }
                    }
                }
            }
            NewReachEngine.setThreadIdsVectorClock(allThreads.toShortArray());
            NewReachEngine.processSyncNode();
        }
    }
}
