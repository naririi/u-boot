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
// RIMOSSO: import semmle.code.cpp.controlflow.Guards  ← causa del crash

class NetworkByteSwap extends Expr {
  NetworkByteSwap() {
    exists(MacroInvocation inv, Macro m |
      inv.getMacro() = m and
      (m.getName() = "ntohs" or
       m.getName() = "ntohl" or
       m.getName() = "ntohll") and
      this = inv.getExpr()
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

  // Usa RelationalOperation invece di GuardCondition
  // Cattura i casi: if (len > MAX), if (len < SIZE), ecc.
  predicate isBarrier(DataFlow::Node node) {
    exists(RelationalOperation cmp |
      cmp.getAnOperand() = node.asExpr()
    )
  }
}

module MyTaint = TaintTracking::Global<MyConfig>;
import MyTaint::PathGraph

from MyTaint::PathNode source, MyTaint::PathNode sink
where MyTaint::flowPath(source, sink)
select sink.getNode(), source, sink,
  "Network byte swap flows to memcpy"