package simplifier

import math.pow
import scala.collection.immutable.::

import AST._

// to implement
// avoid one huge match of cases
// take into account non-greedy strategies to resolve cases with power laws
object Simplifier {

  var variableAssignments:Map[Node,Node] = Map()

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
      simplifiedCond match {
        case FalseConst() => DeadInstr()
        case _ => WhileInstr(simplifiedCond, simplify(body))
      }

    // Removing assignments to itself and shortening x = y if %s else z
    // also checking for a=b; c=b using map - not in specification
    case Assignment(Variable(left), expr) => expr match {
      case Variable(y) if left == y => DeadInstr()
      case _ => expr match {
        // x = y if %s else z
        case IfElseExpr(cond,iLeft,iRight) =>
          Assignment(Variable(left),simplify(IfElseInstr(cond,iLeft,iRight)))
        case Variable(right) => variableAssignments get Variable(right) match {
          case Some(Variable(original)) =>
            variableAssignments += (Variable(left) -> Variable(right) )
            //println(variableAssignments.keys)
            Assignment(Variable(left), Variable(original))
          case None => // Hasn't been assigned yet
            variableAssignments += (Variable(left) -> Variable(right) )
            //println(variableAssignments.keys)
            Assignment(Variable(left), simplify(expr))
          case _ => Assignment(Variable(left), expr)
        }
        case _ => Assignment(Variable(left), simplify(expr))
      }
    }

    // Logical simplifications

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

    case BinExpr("==", x, y) if x == y => TrueConst()
    case BinExpr("!=", x,y)  if x == y => FalseConst()
    case BinExpr(">=", x,y)  if x == y => TrueConst()
    case BinExpr("<=", x,y)  if x == y => TrueConst()
    case BinExpr("<", x,y)   if x == y => FalseConst()
    case BinExpr(">", x,y)   if x == y => FalseConst()
    case BinExpr("or", x ,y) if x == y => x
    case BinExpr("and", x,y) if x == y => x

    case BinExpr("and", left, right) =>
      (simplify(left), simplify(right)) match {
        case (_ , FalseConst()) => FalseConst()
        case (FalseConst(), _) => FalseConst()
        case (expr, TrueConst()) => expr
        case (TrueConst(), expr) => expr
        case (exprLeft, exprRight) if exprLeft == exprRight => exprLeft
        case (exprLeft, exprRight) =>
          if (exprLeft != left || exprRight != right) // Checking if it's the end of simplification
            simplify(BinExpr("and", exprLeft, exprRight))
          else BinExpr("and", exprLeft, exprRight)
      }

    case BinExpr("or", left, right) =>
      (simplify(left), simplify(right)) match {
        case (_ , TrueConst()) => TrueConst()
        case (TrueConst(), _) => TrueConst()
        case (expr, FalseConst()) => expr
        case (FalseConst(), expr) => expr
        case (exprLeft, exprRight) if exprLeft == exprRight => exprLeft
        case (exprLeft, exprRight) =>
          if (exprLeft != left || exprRight != right) // Checking if it's the end of simplification
            simplify(BinExpr("or", exprLeft, exprRight))
          else BinExpr("or", exprLeft, exprRight)
      }


    //        --- Unary expressions ---

    case Unary("not", expr) => expr match {
      case BinExpr("==", left, right) => simplify(BinExpr("!=", left, right))
      case BinExpr("!=", left, right) => simplify(BinExpr("==", left, right))
      case BinExpr("<=", left, right) => simplify(BinExpr(">",  left, right))
      case BinExpr(">=", left, right) => simplify(BinExpr("<",  left, right))
      case BinExpr("<", left, right) => simplify(BinExpr(">=", left, right))
      case BinExpr(">", left, right) => simplify(BinExpr("<=", left, right))

      case TrueConst() => FalseConst()
      case FalseConst() => TrueConst()

      case Unary("not", expr2) => simplify(expr2) // double negation

      case expr2 => Unary("not", simplify(expr2))
    }

    case Unary("-", expr) => expr match {
      case Unary("-", expr2) => simplify(expr2) // --x
      case IntNum(x)         => IntNum(-x)
      case FloatNum(x)       => FloatNum(-x)
      case expr2             => Unary("-", simplify(expr2))
    }

    //Balancing trees ((((l1*r1)+(l2*r2))+(l3*r3))+(l4*r4)) => (((l1*r1)+(l2*r2))+((l3*r3)+(l4*r4)))
    case (BinExpr("+", BinExpr("+", BinExpr("+", BinExpr("*", l1, r1), BinExpr("*", l2, r2)), BinExpr("*", l3, r3)), BinExpr("*", l4, r4)))
    => simplify(BinExpr("+", BinExpr("+", BinExpr("*", l1, r1), BinExpr("*", l2, r2)), BinExpr("+", BinExpr("*", l3, r3), BinExpr("*", l4, r4))))

    //      --- Arithmetic expressions ---

    // Here a duplication for floats was required, cannot create object of generic type
    case BinExpr(op, oLeft, oRight) =>  (simplify(oLeft),simplify(oRight)) match {

      // Reduction of equal arguments
      case (left,right) if left==right =>  op match {
        case "/" | "%" => IntNum(1)
        case "-" => IntNum(0)
        case _ => simplify(BinExpr(op, left, right))
      }

      case (left,right@IntNum(num)) => Integer2int(num) match {
          case 0 => op match {
            case "-" | "+" => left
            case "*" => IntNum(0)
            case "/" | "%" => throw new ArithmeticException(op + " by 0")
            case "**" => IntNum(1)
            case _ => BinExpr(op, left, right)
          }
          case 1 => op match {
            case "*" | "/" | "%" | "**" => left
            case _ => BinExpr(op, left, right)
          }
          case _ => BinExpr(op, left, right )
      }
      case (left,right@FloatNum(num)) => num match {
          case 0 => op match {
            case "-" | "+" => left
            case "*" => FloatNum(0)
            case "/" | "%" => throw new ArithmeticException(op + " by 0")
            case "**" => FloatNum(1)
            case _ => BinExpr(op, left, right)
          }
          case 1 => op match {
            case "*" | "/" | "%" | "**" => left
            case _ => BinExpr(op, left, right)
          }
          case _ => BinExpr(op, left, right )
      }
      // Other way around
      case (left@IntNum(num), right) => Integer2int(num) match  {
          case 0 => op match {
            case "+" => right
            case "-" => simplify(Unary("-", right))
            case "*" => IntNum(0)
            case "**" => IntNum(0)
            case _ => BinExpr(op, left, right)
          }
          case 1 => op match {
            case "*" => right
            case "**" => IntNum(1)
            case _ => BinExpr(op, left, right)
          }
          case _ => BinExpr(op, left, right )
      }
      case (left@FloatNum(num), right) => num match {
          case 0 => op match {
            case "+" => right
            case "-" => simplify(Unary("-", right))
            case "*" => FloatNum(0)
            case "**" => FloatNum(0)
            case _ => BinExpr(op, left, right)
          }
          case 1 => op match {
            case "*" => right
            case "**" => FloatNum(1)
            case _ => BinExpr(op, left,  right)
          }
          case _ => BinExpr(op, left, right )
      }

      // Short multiplication formulas

      case (first@BinExpr("**", BinExpr(op1, x1, y1), IntNum(x)), second@BinExpr("**", BinExpr(op2, x2, y2), IntNum(y)))
        if x1 == x2 && y1 == y2 && x == 2 && y == 2 => (op, op1, op2) match {
        case ("-","+","-") => BinExpr("*", BinExpr("*", x1, IntNum(4)), y1) // (x+y)^2 - (x-y)^2 = 4xy
        case ("-","-","+") => Unary("-", BinExpr("*", BinExpr("*", x1, IntNum(4)), y1)) // (x-y)^2 - (x+y)^2 = -4xy
        case _ => BinExpr("-", simplify(first), simplify(second))
      }

      // TODO: Test
      // (x+y)^2-x^2-2*xy lub (x+y)^2-x^2-2*yx
      case (BinExpr("-", BinExpr("**", BinExpr("+", x1, y1), IntNum(a)), BinExpr("**", x2, IntNum(b))), BinExpr("*", BinExpr("*", x3, IntNum(c)), y3))
        if a == 2 && b == 2 && c == 2 && x1 == x2 && ((x1 == x3 && y1 == y3) || (x1 == y3 && y1 == x3)) && op == "-" =>
        simplify(BinExpr("**", y1, IntNum(2)))

      // TODO: Test
      // (x+y)^2-y^2-2yx lub (x+y)^2-y^2-2xy
      case (BinExpr("-", BinExpr("**", BinExpr("+", x1, y1), IntNum(a)), BinExpr("**", x2, IntNum(b))), BinExpr("*", BinExpr("*", x3, IntNum(c)), y3))
        if a == 2 && b == 2 && c == 2 && y1 == x2 && ((x1 == x3 && y1 == y3) || (x1 == y3 && y1 == x3)) & op == "-" =>
        simplify(BinExpr("**", x1, IntNum(2)))

      // TODO: Test
      //  x^2+2xy+y^2 lub x^2+2yx+y^2
      case (BinExpr("+", BinExpr("**", x1, IntNum(a)), BinExpr("*", BinExpr("*", x2, IntNum(b)), y2)), BinExpr("**", y3, IntNum(c)))
        if a == 2 && b == 2 && c == 2 && ((x1 == y2 && x2 == y3) || (x1 == x2 && y2 == y3)) && op == "+" =>
        simplify(BinExpr("**", BinExpr("+", x1, y3), IntNum(2)))

      // Power laws
      // x^^y*x^z == x^^(y+z) and so on
      case (BinExpr("**", x1, y1), BinExpr("**", x2, y2)) if x1 == x2 && op == "*" =>
        simplify(BinExpr("**", x1, BinExpr("+", y1, y2)))

      case (BinExpr("**", x1, y1), BinExpr("**", x2, y2)) if x1 == x2 && op == "/" =>
        simplify(BinExpr("**", x1, BinExpr("-", y1, y2)))

      // Nominator denominator simplifications
      case (expr, BinExpr("/", numerator, denominator)) if op == "*" => simplify(BinExpr("/", BinExpr("*", expr, numerator), denominator))
      case (BinExpr("/", numerator, denominator), expr) if op == "*" => simplify(BinExpr("/", BinExpr("*", expr, numerator), denominator))

      //  Reduction of type -x+x = x-x
      case (Unary("-", exprU), right) if op == "+" => simplify(BinExpr("-", right, exprU))
      case (left, Unary("-", exprU)) if op == "+" => simplify(BinExpr("-", left, exprU))


      case (extLeft, extRight) => op match {

        case "+" => (extLeft, extRight) match {

          // Commutative property of addition

          case (var1@Variable(name), var2@Variable(name2)) =>
            if (name.compareTo(name2) < 0)
              BinExpr("+",Variable(name),Variable(name2))
            else
              BinExpr("+",Variable(name2),Variable(name))

          // Distributive property of multiplication:

          case (left@BinExpr("*", l1, r1), right@BinExpr("*", l2, r2)) =>
            if (l1 == l2) BinExpr("*", BinExpr("-", r1, r2), l1) // (a*b)+(a*c)
            else if (r1 == r2) BinExpr("*", BinExpr("-", l1, l2), r1) // (a*b)+(c*b)
            else if (l1 == r2) BinExpr("*", BinExpr("-", r1, l2), l1) // (a*b)+(c*a)
            else BinExpr("*", BinExpr("-", l1, r2), r1) // (a*b)+(b*c)


          case (BinExpr("*", inLeft, inRight), right) if right == inLeft => // a*b+a = a(b+1)
            simplify(BinExpr("*", BinExpr("+", inRight, IntNum(1)), inLeft))
          case (BinExpr("*", inLeft, inRight), right) if right == inRight => // a*b+b = b(a+1)
            simplify(BinExpr("*", BinExpr("+", inLeft, IntNum(1)), inRight))

          // Distributive properties of division :

          case (left@BinExpr("/", l1, r1), right@BinExpr("/", l2, r2)) =>

            if (r1 == r2) BinExpr("/", BinExpr("+", l1, l2), r1) // (x/y)+(z/y) = (x+z)/y
            else {
              val s1 = simplify(left)
              val s2 = simplify(right)
              if (s1 != left || s2 != right) simplify(BinExpr("+", s1, s2)) else BinExpr("+", s1, s2)
            }

          // Associative properties of addition and subtraction:

          case (left@BinExpr("-", inLeft, inRight), right) =>
            if (inRight == right) simplify(inLeft)   // (x-y)+y
            else BinExpr("+", simplify(left), simplify(right))
          case (left, right@BinExpr("-", inLeft, inRight)) =>
            if (inRight == left) simplify(inLeft)   // (x-y)+y
            else BinExpr("+", simplify(left), simplify(right))
          case (left, right) =>
            // Checking if simplification goes further
            val sL = simplify(left)
            val sR = simplify(right)
            if (sL != left || sR != right) simplify(BinExpr("+", sL, sR)) else BinExpr("+", sL, sR)
        }
        case "-" => (extLeft, extRight) match {

          // Distributive property of multiplication:

          case (left@BinExpr("*", l1, r1), right@BinExpr("*", l2, r2)) =>
            if (l1 == l2) BinExpr("*", BinExpr("-", r1, r2), l1) // (a*b)-(a*c)
            else if (r1 == r2) BinExpr("*", BinExpr("-", l1, l2), r1) // (a*b)-(c*b)
            else if (l1 == r2) BinExpr("*", BinExpr("-", r1, l2), l1) // (a*b)-(c*a)
            else BinExpr("*", BinExpr("-", l1, r2), r1) // (a*b)-(b*c)

          case (BinExpr("*", inLeft, inRight), right) if right == inLeft => // a*b-a = a(b-1)
            simplify(BinExpr("*", BinExpr("-", inRight, IntNum(1)), inLeft))
          case (BinExpr("*", inLeft, inRight), right) if right == inRight => // a*b-b = b(a-1)
            simplify(BinExpr("*", BinExpr("-", inLeft, IntNum(1)), inRight))


          // Distributive properties of division :

          case (e1@BinExpr("/", l1, r1), e2@BinExpr("/", l2, r2)) =>
            if (r1 == r2) BinExpr("/", BinExpr("-", l1, l2), r1) // (x/y)-(z/y) = (x-z)/y
            else {
              val s1 = simplify(e1)
              val s2 = simplify(e2)
              if (s1 != e1 || s2 != e2) simplify(BinExpr("-", s1, s2)) else BinExpr("-", s1, s2)
            }

          // Associative properties of addition and subtraction:

          case (left@BinExpr("+", inLeft, inRight), right) =>
            if (inLeft == right) simplify(inRight)            // (x+y)-x
            else if (inRight == right) simplify(inLeft)       // (x+y)-y
            else BinExpr("-", simplify(left), simplify(right))
          case (left, right@BinExpr("+", inLeft, inRight)) =>
            if (inLeft == left) simplify(Unary("-", inRight)) // x-(x+y)
            else if (inRight == left) simplify(Unary("-", inLeft)) // y-(x+y)
            else BinExpr("-", simplify(left), simplify(right))
          case (left, right) =>
            // Checking if simplification goes further
            val sL = simplify(left)
            val sR = simplify(right)
            if (sL != left || sR != right) simplify(BinExpr("-", sL, sR)) else BinExpr("-", sL, sR)
        }
        // Power laws
        case "**" => (extLeft, extRight) match {
          case (BinExpr("**", inLeft, inRight), right) =>
            simplify(BinExpr("**", inLeft, BinExpr("*", inRight, right))) // a**b**c = a**(b*c)
          case (left, right) =>
            // Checking if simplification goes further
            val sL = simplify(left)
            val sR = simplify(right)
            if (sL != left || sR != right) simplify(BinExpr("**", sL, sR)) else BinExpr("**", sL, sR)
        }
        case _ =>
          // Checking if simplification goes further
          val sLeft = simplify(extLeft)
          val sRight = simplify(extRight)
          if (sLeft != extLeft || sRight != extRight) simplify(BinExpr(op, sLeft, sRight)) else BinExpr(op, sLeft, sRight)
      }
    }

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
      // ----------- Peephole optimization x=a; x=b => x=b -------------

      //   TODO: Moze da sie to zrobic piekniej - 8 kombinacji

      case (Assignment(fLeft, fRight):: Assignment(left, right) :: Nil) => fLeft match {
        case `left` => NodeList(simplify(Assignment(fLeft, right)) :: Nil)
      }
      case (Assignment(fLeft, fRight):: Assignment(left, right) :: rest) => fLeft match {
        case `left` => NodeList((Assignment(fLeft, right) :: rest) map simplify)
      }
      case (Assignment(fLeft, fRight):: middle :: Assignment(left, right) :: Nil) => fLeft match {
        case `left` => NodeList((middle :: Assignment(fLeft, right) :: Nil) map simplify)
      }
      case (Assignment(fLeft, fRight):: middle :: Assignment(left, right) :: rest) => fLeft match {
        case `left` => NodeList((middle :: Assignment(fLeft, right) :: rest) map simplify)
      }
      case (head :: Assignment(fLeft, fRight) :: Assignment(left, right) :: Nil) => fLeft match {
        case `left` => NodeList((head :: Assignment(fLeft, right) :: Nil) map simplify)
      }
      case (head :: Assignment(fLeft, fRight):: Assignment(left, right) :: rest) => fLeft match {
        case `left` => NodeList((head :: Assignment(fLeft, right) :: rest) map simplify)
      }
      case (head :: Assignment(fLeft, fRight):: middle :: Assignment(left, right) :: Nil) => fLeft match {
        case `left` => NodeList((head :: middle :: Assignment(fLeft, right) :: Nil) map simplify)
      }
      case (head :: Assignment(fLeft, fRight):: middle :: Assignment(left, right) :: rest) => fLeft match {
        case `left` => NodeList((head :: middle :: Assignment(fLeft, right) :: rest) map simplify)
      }


      case _ => NodeList(list map simplify)
    }


    case ElemList(list) => ElemList(list map simplify)

    case Tuple(list) => Tuple(list map simplify)

    // Nothing can be simplified:
    case `node` => node;
  }
}
