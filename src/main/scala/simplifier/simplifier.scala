package simplifier

import math.pow
import scala.math.Ordered._

import AST._

// to implement
// avoid one huge match of cases
// take into account non-greedy strategies to resolve cases with power laws
object Simplifier {


  def parseArithmetic[T](op: String, x: T, y: T)(implicit n: Numeric[T]): T = op match {
    case "+" => new T(n.plus(x,y))
    case "-" => new T(n.minus(x,y))
    case "*" => new T(n.times(x,y))
    case "/" => new T(n.toDouble(x)/n.toDouble(y))
    case "%" => new T(n.toInt(x)%n.toInt(y))
    case "**" => new T(pow(n.toDouble(x), n.toDouble(y)).toInt)
  }

  // A bit of magic
  // https://stackoverflow.com/questions/19385235/how-to-paramaterize-int-as-ordered-in-scala
  def parseCompare[T](op: String, x: T, y: T)(implicit ordering: Ordering[T]): Node = op match {
    case "==" => if (ordering.eq(x,y)) TrueConst() else FalseConst()
    case "!=" => if (!ordering.eq(x,y)) TrueConst() else FalseConst()
    case "<" => if (ordering.lt(x,y)) TrueConst() else FalseConst()
    case "<=" => if (ordering.lteq(x,y)) TrueConst() else FalseConst()
    case ">" => if (ordering.gt(x,y))   TrueConst() else FalseConst()
    case ">=" => if (ordering.gteq(x,y))   TrueConst() else FalseConst()
  }

  def simplify(node: Node): Node = node match {

    // Concatenating lists and tuples
    case BinExpr("+", Tuple(first), Tuple(second)) => Tuple((first ++ second) map simplify)
    case BinExpr("+", ElemList(first), ElemList(second)) => ElemList((first ++ second) map simplify)

    // Removing duplicates from dictionaries
    // It associates keys of keyDatums with the whole objects,
    // then maps the resulting list to objects, leaving out duplicates
    case KeyDatumList(list) => KeyDatumList(list.foldLeft(Map.empty[Node, KeyDatum])(
      (map, keyDatum) => map + (keyDatum.key -> keyDatum)
    ).toList.map(x => x._2))

    // Removing if's with false condition
    case IfElseInstr(cond, left, right) =>
      val simplifiedCondition = simplify(cond)
      simplifiedCondition match {
        case TrueConst()  => simplify(left)
        case FalseConst() => simplify(right)
        case _            => IfElseInstr(simplifiedCondition, simplify(left), simplify(right))
      }

    case IfInstr(cond, left) =>
      val simplifiedCondition = simplify(cond)
      simplifiedCondition match {
        case TrueConst()  => simplify(left)
        case FalseConst() => DeadInstr()
        case _            => IfInstr(simplifiedCondition, simplify(left))
      }

    // Removing loops with false condition
    case WhileInstr(cond, body) =>
      val simplifiedCond = simplify(cond)
      simplifiedCond match {
        case FalseConst() => DeadInstr()
        case _ => WhileInstr(simplifiedCond, simplify(body))
      }

    // Removing assignments to itself
    case Assignment(Variable(x), expr) => expr match {
      case Variable(y) if x == y => DeadInstr()
      case _ => Assignment(Variable(x), simplify(expr))
    }

    case BinExpr(op, IntNum(x), IntNum(y)) =>
      op match {

        case "==" | "!="| ">"| ">="| "<"| "<=" => parseCompare[Integer](op,x,y)
      }

    case BinExpr(op, FloatNum(x), FloatNum(y)) =>
      op match {
        case "==" | "!="| ">"| ">="| "<"| "<=" => parseCompare[Double](op,x,y)
      }

    case BinExpr(op, IntNum(x), FloatNum(y)) =>
      op match {
        case "==" | "!="| ">"| ">="| "<"| "<=" => parseCompare[Double](op,x.doubleValue(),y)
      }

    case BinExpr(op, FloatNum(x), IntNum(y)) =>
      op match {
        case "==" | "!="| ">"| ">="| "<"| "<=" => parseCompare[Double](op,x,y.doubleValue())
      }


//    Don't know how to do this
//    case FunDef(fun) => fun match {
//      case (name, formal_args, body) => FunDef(name, simplify(formal_args), simplify(body))
//    }

    case NodeList(list) => NodeList(list map simplify)

    // Nothing can be simplified:
//    case node => StringConst(node.getClass.toString)
    case node => node;
  }
}
