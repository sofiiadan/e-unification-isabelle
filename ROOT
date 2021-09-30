chapter "E-Unification"

session Logging in "Logging" = "Pure" +
  theories
    Logging

session E_Unification = "Pure" +
  sessions
    Logging

  theories
    E_Unification

session E_Unification_Tests in "Tests" = "HOL" +
  sessions
    SpecCheck
    E_Unification

  directories
    "../Examples"

  theories
    First_Order_Unification_Tests
    Higher_Order_Pattern_Unification_Tests
    Unification_Hints_Examples
