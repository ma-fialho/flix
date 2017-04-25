namespace TestImplicits {

    namespace Test01 {
        rel A(x: Int, implicit b: Bool)
        rel R(x: Int, implicit b: Bool)

        A(21, true).
        A(42, false).

        R(x) :- A(x).                               // equivalent to R(x, b) :- A(x, b).
    }

    namespace Test02 {
        rel A(x: Int, implicit b: Bool)
        rel R(x: Int, implicit b: Bool)

        A(21, true).
        A(42, false).

        R(x, b) :- A(x, b).                         // direct style, no implicits
    }

    namespace Test03 {
        rel A(x: Int, y: Int, implicit b: Bool)
        rel R(x: Int, implicit b: Bool)

        A(21, 21, true).
        A(42, 42, false).

        R(x) :- A(x, 21).                           // equivalent to R(x, b) :- A(x, 21, b).
    }

    namespace Test04 {
        rel A(x: Int, implicit b: Bool)
        rel B(x: Int, implicit b: Bool)
        rel R(x: Int)

        A(21, true).
        A(42, false).
        B(21, true).

        R(x) :- A(x), B(x).                         // equivalent to R(x) :- A(x, b), B(x, b).
    }

    namespace Test05 {
        rel A(x: Int, implicit b: Bool)
        rel B(x: Int, implicit b: Bool)
        rel C(x: Int, implicit b: Bool)
        rel R(x: Int)

        A(21, true).
        A(42, false).
        B(21, true).
        C(21, true).

        R(x) :- A(x), B(x), C(x).                   // equivalent to R(x) :- A(x, b), B(x, b), C(x, b).
    }

    namespace Test06 {
        rel A(x: Int, implicit b: Bool, implicit c: Char)
        rel R(x: Int, implicit b: Bool, implicit c: Char)

        A(21, true, 'a').
        A(42, false, 'b').

        R(x) :- A(x).                               // equivalent to R(x, b, c) :- A(x, b, c).
    }

    namespace Test07 {
        rel A(x: Int, implicit b: Bool, implicit c: Char)
        rel B(x: Int, implicit b: Bool, implicit c: Char)
        rel R(x: Int, implicit b: Bool, implicit c: Char)

        A(21, true, 'a').
        A(42, false, 'b').
        B(42, false, 'b').

        R(x) :- A(x), B(x).                         // equivalent to R(x, b, c) :- A(x, b, c), B(x, b, c).
    }

    namespace Test08 {
        rel A(implicit x: Int, b: Bool, implicit c: Char)
        rel B(implicit x: Int, b: Bool, implicit c: Char)
        rel R(implicit x: Int, b: Bool, implicit c: Char)

        A(21, true, 'a').
        A(42, false, 'b').
        B(42, false, 'b').

        R(b) :- A(b), B(b).                         // equivalent to R(x, b, c) :- A(x, b, c), B(x, b, c).
    }




}