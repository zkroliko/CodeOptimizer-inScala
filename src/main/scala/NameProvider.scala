package Name

import AST._

object NameProvider {

  def name(node: Node): String = node match {

    case Variable(name) => name;

    case BinExpr("+",Variable(name1),Variable(name2)) => name1+name2

    case BinExpr("*",Variable(name1),Variable(name2)) => name1+name2

    case BinExpr("+",left:BinExpr,right:BinExpr) => name(left) concat name(right)

    case BinExpr("*",left:BinExpr,right:BinExpr) => name(left) concat name(right)

    // Nothing can be simplified:
    case node => node.toStr;
  }


}
