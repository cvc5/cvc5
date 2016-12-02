; COMMAND-LINE: --fmf-fun-rlv --no-check-models
; EXPECT: sat
(set-logic ALL_SUPPORTED)
(define-fun $$isTrue$$ ((b Bool)) Bool b)
(define-fun $$isFalse$$ ((b Bool)) Bool (not b))
(define-fun $$toString$$ ((b Bool)) String (ite b "true" "false") )
(define-fun $$fromString$$ ((s String)) Bool (= s "true") )
(define-fun $$inttostr$$ ((i Int)) String (ite (< i 0) (str.++ "-" (int.to.str (- i))) (int.to.str i)))
(declare-fun $$takeWhile$$ (String String) String)
(declare-fun $$takeWhileNot$$ (String String) String)
(declare-fun $$dropWhile$$ (String String) String)
(declare-fun $$dropWhileNot$$ (String String) String)
(declare-datatypes () (
    (AddressType (AddressType$C_AddressType (AddressType$C_AddressType$address String) (AddressType$C_AddressType$city String) (AddressType$C_AddressType$region String) (AddressType$C_AddressType$postalCode String) (AddressType$C_AddressType$country String)))
    (Conditional_Int (Conditional_Int$CAbsent_Int) (Conditional_Int$CPresent_Int (Conditional_Int$CPresent_Int$value Int)))
    (Conditional_dateTime (Conditional_dateTime$CAbsent_dateTime) (Conditional_dateTime$CPresent_dateTime (Conditional_dateTime$CPresent_dateTime$value Int)))
    (Conditional_string (Conditional_string$CAbsent_string) (Conditional_string$CPresent_string (Conditional_string$CPresent_string$value String)))
    (CustomerType (CustomerType$C_CustomerType (CustomerType$C_CustomerType$companyName String) (CustomerType$C_CustomerType$contactName String) (CustomerType$C_CustomerType$contactTitle String) (CustomerType$C_CustomerType$phone String) (CustomerType$C_CustomerType$fax Conditional_string) (CustomerType$C_CustomerType$fullAddress AddressType) (CustomerType$C_CustomerType$customerID Int)))
    (List_CustomerType (List_CustomerType$CNil_CustomerType) (List_CustomerType$Cstr_CustomerType (List_CustomerType$Cstr_CustomerType$head CustomerType) (List_CustomerType$Cstr_CustomerType$tail List_CustomerType)))
    (List_OrderType (List_OrderType$CNil_OrderType) (List_OrderType$Cstr_OrderType (List_OrderType$Cstr_OrderType$head OrderType) (List_OrderType$Cstr_OrderType$tail List_OrderType)))
    (OrderType (OrderType$C_OrderType (OrderType$C_OrderType$customerID Int) (OrderType$C_OrderType$employeeID Int) (OrderType$C_OrderType$orderDate Int) (OrderType$C_OrderType$requiredDate Int) (OrderType$C_OrderType$shipInfo ShipInfoType)))
    (RootType (RootType$C_RootType (RootType$C_RootType$customers List_CustomerType) (RootType$C_RootType$orders List_OrderType)))
    (ShipInfoType (ShipInfoType$C_ShipInfoType (ShipInfoType$C_ShipInfoType$shipVia Int) (ShipInfoType$C_ShipInfoType$freight Int) (ShipInfoType$C_ShipInfoType$shipName String) (ShipInfoType$C_ShipInfoType$shipAddress String) (ShipInfoType$C_ShipInfoType$shipCity String) (ShipInfoType$C_ShipInfoType$shipRegion String) (ShipInfoType$C_ShipInfoType$shipPostalCode String) (ShipInfoType$C_ShipInfoType$shipCountry String) (ShipInfoType$C_ShipInfoType$shippedDate Conditional_dateTime)))
) )

(define-fun f2866$toXml((a$$2869 AddressType)) String (str.++ (str.++ (str.++ (str.++ (str.++ (str.++ (str.++ (str.++ (str.++ (str.++ (str.++ (str.++ (str.++ (str.++ (str.++ (str.++ "<FullAddress>" "<Address>") (AddressType$C_AddressType$address a$$2869)) "</Address>") "<City>") (AddressType$C_AddressType$city a$$2869)) "</City>") "<Region>") (AddressType$C_AddressType$region a$$2869)) "</Region>") "<PostalCode>") (AddressType$C_AddressType$postalCode a$$2869)) "</PostalCode>") "<Country>") (AddressType$C_AddressType$country a$$2869)) "</Country>") "</FullAddress>"))
(define-fun f2656$toXml((c$$2659 CustomerType)) String (str.++ (str.++ (str.++ (str.++ (str.++ (str.++ (str.++ (str.++ (str.++ (str.++ (str.++ (str.++ (str.++ (str.++ (str.++ (str.++ (str.++ "<Customer CustomerID=" ($$inttostr$$ (CustomerType$C_CustomerType$customerID c$$2659))) ">") "<CompanyName>") (CustomerType$C_CustomerType$companyName c$$2659)) "</CompanyName>") "<ContactName>") (CustomerType$C_CustomerType$contactName c$$2659)) "</ContactName>") "<ContactTitle>") (CustomerType$C_CustomerType$contactTitle c$$2659)) "</ContactTitle>") "<Phone>") (CustomerType$C_CustomerType$phone c$$2659)) "</Phone>") (ite (is-Conditional_string$CPresent_string (CustomerType$C_CustomerType$fax c$$2659)) (str.++ (str.++ "<Fax>" (Conditional_string$CPresent_string$value (CustomerType$C_CustomerType$fax c$$2659))) "</Fax>") "")) (f2866$toXml (CustomerType$C_CustomerType$fullAddress c$$2659))) "</Customer>"))
(define-funs-rec
  (
    (f2574$toXml((lc$$2577 List_CustomerType)) String)
  )
  (
    (ite (is-List_CustomerType$CNil_CustomerType lc$$2577) "" (str.++ (f2656$toXml (List_CustomerType$Cstr_CustomerType$head lc$$2577)) (f2574$toXml (List_CustomerType$Cstr_CustomerType$tail lc$$2577))))
  )
)
(define-fun f2942$toXml((s$$2945 ShipInfoType)) String (str.++ (str.++ (str.++ (str.++ (str.++ (str.++ (str.++ (str.++ (str.++ (str.++ (str.++ (str.++ (str.++ (str.++ (str.++ (str.++ (str.++ (str.++ (str.++ (str.++ (str.++ (str.++ (str.++ (str.++ (str.++ (str.++ "<ShipInfo" (ite (is-Conditional_dateTime$CPresent_dateTime (ShipInfoType$C_ShipInfoType$shippedDate s$$2945)) (str.++ (str.++ " ShippedDate=" ($$inttostr$$ (Conditional_dateTime$CPresent_dateTime$value (ShipInfoType$C_ShipInfoType$shippedDate s$$2945)))) ">") ">")) "<ShipVia>") ($$inttostr$$ (ShipInfoType$C_ShipInfoType$shipVia s$$2945))) "</ShipVia>") "<Freight>") ($$inttostr$$ (ShipInfoType$C_ShipInfoType$freight s$$2945))) "</Freight>") "<ShipName>") (ShipInfoType$C_ShipInfoType$shipName s$$2945)) "</ShipName>") "<ShipAddress>") (ShipInfoType$C_ShipInfoType$shipAddress s$$2945)) "</ShipAddress>") "<ShipCity>") (ShipInfoType$C_ShipInfoType$shipCity s$$2945)) "</ShipCity>") "<ShipRegion>") (ShipInfoType$C_ShipInfoType$shipRegion s$$2945)) "</ShipRegion>") "<ShipPostalCode>") (ShipInfoType$C_ShipInfoType$shipPostalCode s$$2945)) "</ShipPostalCode>") "<ShipCountry>") (ShipInfoType$C_ShipInfoType$shipCountry s$$2945)) "</ShipCountry>") "</ShipInfo>"))
(define-fun f2776$toXml((o$$2779 OrderType)) String (str.++ (str.++ (str.++ (str.++ (str.++ (str.++ (str.++ (str.++ (str.++ (str.++ (str.++ (str.++ (str.++ (str.++ "<Order>" "<CustomerID>") ($$inttostr$$ (OrderType$C_OrderType$customerID o$$2779))) "</CustomerID>") "<EmployeeID>") ($$inttostr$$ (OrderType$C_OrderType$employeeID o$$2779))) "</EmployeeID>") "<OrderDate>") ($$inttostr$$ (OrderType$C_OrderType$orderDate o$$2779))) "</OrderDate>") "<RequiredDate>") ($$inttostr$$ (OrderType$C_OrderType$requiredDate o$$2779))) "</RequiredDate>") (f2942$toXml (OrderType$C_OrderType$shipInfo o$$2779))) "</Order>"))
(define-funs-rec
  (
    (f2615$toXml((lo$$2618 List_OrderType)) String)
  )
  (
    (ite (is-List_OrderType$CNil_OrderType lo$$2618) "" (str.++ (f2776$toXml (List_OrderType$Cstr_OrderType$head lo$$2618)) (f2615$toXml (List_OrderType$Cstr_OrderType$tail lo$$2618))))
  )
)
(define-fun f2526$toXml((r$$2529 RootType)) String (str.++ (str.++ (str.++ (str.++ (str.++ (str.++ (str.++ "<Root>" "<Customers>") (f2574$toXml (RootType$C_RootType$customers r$$2529))) "</Customers>") "<Orders>") (f2615$toXml (RootType$C_RootType$orders r$$2529))) "</Orders>") "</Root>"))

(declare-fun $Report$3105$0$1$() String)
(assert (= $Report$3105$0$1$ "<Root><Customers></Customers><Orders></Orders></Root>"))
; should be fast since functions introduced by define-fun-rec do not appear in the ground assertion
(check-sat)

