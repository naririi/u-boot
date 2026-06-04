import cpp
import semmle.code.cpp.dataflow.TaintTracking
import semmle.code.cpp.controlflow.Guards

class NetworkByteSwap extends Expr {
      NetworkByteSwap () {
    // TODO: replace <class> and <var> 
    exists(MacroInvocation inv, Macro m | inv.getMacro() = m and (m.getName() = "ntohs" or m.getName() = "ntohl" or m.getName() = "ntohll")
      // TODO: <condition>
      and this = inv.getExpr()
      )
  }
}

module MyConfig implements DataFlow::ConfigSig {

  predicate isSource(DataFlow::Node source) {
    // TODO
    source.asExpr() instanceof NetworkByteSwap
  }
  predicate isSink(DataFlow::Node sink) {
    // TODO
    exists(FunctionCall call |
    call.getTarget().getName() = "memcpy" and
    sink.asExpr() = call.getArgument(2)
  )
  }
  predicate isBarrier(DataFlow::Node node) {
    exists(GuardCondition gc |
      gc.getAChild*() = node.asExpr()
    )
  }
  
}
module MyTaint = TaintTracking::Global<MyConfig>;
import MyTaint::PathGraph

from MyTaint::PathNode source, MyTaint::PathNode sink
where MyTaint::flowPath(source, sink) 
select sink, source, sink, "Network byte swap flows to memcpy"