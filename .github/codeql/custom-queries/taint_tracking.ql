/**
 * @name Network byte swap flows to memcpy
 * @kind path-problem
 * @id cpp/network-memcpy
 * @problem.severity error
 * @security-severity 9.0
 * @tags security
 */

import cpp
import semmle.code.cpp.dataflow.new.DataFlow
import semmle.code.cpp.dataflow.new.TaintTracking

class NetworkByteSwap extends Expr {
  NetworkByteSwap() {
    exists(MacroInvocation inv, Macro m |
      inv.getMacro() = m and
      (m.getName() = "ntohs" or
       m.getName() = "ntohl" or
       m.getName() = "ntohll") and
      this = inv.getExpr() and
      // FIX 1: escludi invocazioni già dentro un'altra macro ntoh*
      // (evita di contare due volte la stessa)
      not exists(MacroInvocation outer |
        (outer.getMacro().getName() = "ntohs" or
         outer.getMacro().getName() = "ntohl" or
         outer.getMacro().getName() = "ntohll") and
        outer != inv and
        inv.getExpr().getParent+() = outer.getExpr()
      )
    )
  }
}

module MyConfig implements DataFlow::ConfigSig {
  predicate isSource(DataFlow::Node source) {
    source.asExpr() instanceof NetworkByteSwap
  }

  predicate isSink(DataFlow::Node sink) {
    exists(FunctionCall call |
      call.getTarget().getName() = "memcpy" and
      sink.asExpr() = call.getArgument(2)
    )
  }

  // FIX 2: barrier più robusta — usa getAChild+ invece di getAnOperand
  // per catturare anche espressioni nidificate nelle comparazioni
  predicate isBarrier(DataFlow::Node node) {
    exists(RelationalOperation rel |
      rel.getAChild+() = node.asExpr()
    )
    or
    exists(EqualityOperation eq |    // cattura anche == e !=
      eq.getAChild+() = node.asExpr()
    )
  }
}

module MyTaint = TaintTracking::Global<MyConfig>;
import MyTaint::PathGraph

from MyTaint::PathNode source, MyTaint::PathNode sink
where MyTaint::flowPath(source, sink)
select sink.getNode(), source, sink,
  "Network byte swap flows to memcpy"