package simplifier

import math.pow
import scala.Int
import scala.math.Ordered._

import AST._

// to implement
// avoid one huge match of cases
// take into account non-greedy strategies to resolve cases with power laws
object Simplifier {


  def parseIntArithmetic(op: String, x: Int, y: Int) = op match {
    case "+" => IntNum(x+y)
    case "-" => IntNum(x-y)
    case "*" => IntNum(x*y)
    case "/" => IntNum(x/y)
    case "%" => IntNum(x%y)
    case "**" => IntNum(pow(x.toDouble, y.toDouble).toInt)
  }

  def parseDoubleArithmetic(op: String, x: Double, y: Double) = op match {
    case "+" => FloatNum(x+y)
    case "-" => FloatNum(x-y)
    case "*" => FloatNum(x*y)
    case "/" => FloatNum(x/y)
    case "%" => FloatNum(x%y)
    case "**" => FloatNum(pow(x, y))
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
      println (cond + "=>" + simplify(cond))
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
        case "+" | "-"| "*"| "/"| "%"| "**" => parseIntArithmetic(op,x,y)
        case "==" | "!="| ">"| ">="| "<"| "<=" => parseCompare[Integer](op,x,y)
      }

    case BinExpr(op, FloatNum(x), FloatNum(y)) =>
      op match {
        case "+" | "-"| "*"| "/"| "%"| "**" => parseDoubleArithmetic(op,x,y)
        case "==" | "!="| ">"| ">="| "<"| "<=" => parseCompare[Double](op,x,y)
      }

    case BinExpr(op, IntNum(x), FloatNum(y)) =>
      op match {
        case "+" | "-"| "*"| "/"| "%"| "**" => parseDoubleArithmetic(op,x.doubleValue(),y)
        case "==" | "!="| ">"| ">="| "<"| "<=" => parseCompare[Double](op,x.doubleValue(),y)
      }

    case BinExpr(op, FloatNum(x), IntNum(y)) =>
      op match {
        case "+" | "-"| "*"| "/"| "%"| "**" => parseDoubleArithmetic(op,x,y.doubleValue())
        case "==" | "!="| ">"| ">="| "<"| "<=" => parseCompare[Double](op,x,y.doubleValue())
      }

    // Here a duplication for floats was required, cannot create object of generic type
    case BinExpr(op, Variable(name), IntNum(num)) =>
      Integer2int(num) match {
        case 0 => op match {
          case "-" | "+" => Variable(name)
          case "*" => DeadInstr()
          case "/" | "%" => throw new ArithmeticException(op + " by 0")
          case "**" => IntNum(1)
          case _ => BinExpr(op, Variable(name), IntNum(num))
        }
        case 1 => op match {
          case "*" | "/" | "%" | "**" => Variable(name)
          case _ => BinExpr(op, Variable(name), IntNum(num))
        }
        case _ => BinExpr(op, Variable(name), IntNum(num))
      }

    // Other way around
    case BinExpr(op, IntNum(num), Variable(name)) =>
      Integer2int(num) match {
        case 0 => op match {
          case "-" | "+" => Variable(name)
          case "*" => DeadInstr()
          case "**" => IntNum(0)
          case _ => BinExpr(op, Variable(name), IntNum(num))
        }
        case 1 => op match {
          case "*" => Variable(name)
          case "**" => IntNum(1)
          case _ => BinExpr(op, Variable(name), IntNum(num))
        }
        case _ => BinExpr(op, Variable(name), IntNum(num))
      }

    case BinExpr(op, Variable(name), FloatNum(num)) =>
      num match {
        case 0 => op match {
          case "-" | "+" => Variable(name)
          case "*" => DeadInstr()
          case "/" | "%" => throw new ArithmeticException(op + " by 0")
          case "**" => FloatNum(1)
          case _ => BinExpr(op, Variable(name), FloatNum(num))
        }
        case 1 => op match {
          case "*" | "/" | "%" | "**" => Variable(name)
          case _ => BinExpr(op, Variable(name), FloatNum(num))
        }
        case _ => BinExpr(op, Variable(name), FloatNum(num))
      }

    // Other way around
    case BinExpr(op, FloatNum(num), Variable(name)) =>
      num match {
        case 0 => op match {
          case "-" | "+" => Variable(name)
          case "*" => DeadInstr()
          case "**" => FloatNum(0)
          case _ => BinExpr(op, Variable(name), FloatNum(num))
        }
        case 1 => op match {
          case "*" => Variable(name)
          case "**" => FloatNum(1)
          case _ => BinExpr(op, Variable(name), FloatNum(num))
        }
        case _ => BinExpr(op, Variable(name), FloatNum(num))
    }

//    case BinExpr(op, Variable(first), Variable(second)) => first match {
//      case second => op match {
//        case "/" | "%" => IntNum(1)
//      }
//    }

    case Variable(name) => name match {
      case _ => Variable(name);
    }

    case KeyDatum(key,value) =>
      KeyDatum(key,simplify(value))

    case FunDef(name,args,body) =>
      FunDef(name,simplify(args),simplify(body))

    case FunCall(name,args) =>
      FunCall(name,simplify(args))

    case PrintInstr(expr) =>
      PrintInstr(simplify(expr))

    case LambdaDef(args,body) =>
      LambdaDef(simplify(args),simplify(body))

    case ClassDef(name,inh,suite) =>
      ClassDef(name,inh,simplify(suite))

    case NodeList(list) => list match {
      case Nil => DeadInstr()
      // One element list
      case (first :: Nil) => first match {
        case DeadInstr() => DeadInstr()
        case NodeList(list) => simplify(NodeList(list map simplify))
        case node =>
          val simplifiedN = simplify(node)
          if (simplifiedN != node) simplify(NodeList(List(simplify(node)))) else NodeList(List(simplifiedN))
      }
      case _ => NodeList(list map simplify)
    }

    case ElemList(list) => ElemList(list map simplify)

    case Tuple(list) => Tuple(list map simplify)

    // Nothing can be simplified:
//    case node => StringConst(node.getClass.toString)
    case node => node;
  }
}
