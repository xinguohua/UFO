package trace;

public class FuncExitNode extends AbstractNode {

  public FuncExitNode(short tid, long order) {
    super(tid, order);
  }
  
  @Override
  public String toString() {
    return "gid: "+gid + " #" + tid + " FuncExit" + " order: " +  order;
  }
}
