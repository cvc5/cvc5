// Removing old cardinality implementation, dumping it here.

///////////////////////////////////////////////////////////////
// Commenting out processCard, creates confusion when writing
// processCard2
///////////////////////////////////////////////////////////////


// void TheorySetsPrivate::processCard(Theory::Effort level) {
//   if(level != Theory::EFFORT_FULL) return;


//   Trace("sets-card") << "[sets-card] processCard( " << level << ")" << std::endl;
//   Trace("sets-card") << "[sets-card]   # processed terms = " << d_processedCardTerms.size() << std::endl;
//   Trace("sets-card") << "[sets-card]   # processed pairs = " << d_processedCardPairs.size() << std::endl;
//   NodeManager* nm = NodeManager::currentNM();

//   bool newLemmaGenerated = false;
  
//   // Introduce lemma
//   for(typeof(d_cardTerms.begin()) it = d_cardTerms.begin();
//       it != d_cardTerms.end(); ++it) {

//     for(eq::EqClassIterator j(d_equalityEngine.getRepresentative((*it)[0]), &d_equalityEngine);
//         !j.isFinished(); ++j) {

//       Node n = nm->mkNode(kind::CARD, (*j));

//       if(d_processedCardTerms.find(n) != d_processedCardTerms.end()) {
//         continue;
//       }

//       Trace("sets-card") << "[sets-card]  Processing " << n << " in eq cl of " << (*it) << std::endl;

//       newLemmaGenerated = true;
//       d_processedCardTerms.insert(n);
      
//       Kind k = n[0].getKind();

//       if(k == kind::SINGLETON) {
//         d_external.d_out->lemma(nm->mkNode(kind::EQUAL,
//                                            n,
//                                            nm->mkConst(Rational(1))));
//         continue;
//       } else {
//         d_external.d_out->lemma(nm->mkNode(kind::GEQ,
//                                            n,
//                                            nm->mkConst(Rational(0))));
//       }

//       // rest of the processing is for compound terms
//       if(k != kind::UNION && k != kind::INTERSECTION && k != kind::SETMINUS) {
//         continue;
//       }
  
//       Node s = min(n[0][0], n[0][1]);
//       Node t = max(n[0][0], n[0][1]);
//       bool isUnion = (k == kind::UNION);
//       Assert(Rewriter::rewrite(s) == s);
//       Assert(Rewriter::rewrite(t) == t);

//       typeof(d_processedCardPairs.begin()) processedInfo = d_processedCardPairs.find(make_pair(s, t));

//       if(processedInfo == d_processedCardPairs.end()) {

//         Node sNt = nm->mkNode(kind::INTERSECTION, s, t);
//         sNt = Rewriter::rewrite(sNt);
//         Node sMt = nm->mkNode(kind::SETMINUS, s, t);
//         sMt = Rewriter::rewrite(sMt);
//         Node tMs = nm->mkNode(kind::SETMINUS, t, s);
//         tMs = Rewriter::rewrite(tMs);

//         Node card_s = nm->mkNode(kind::CARD, s);
//         Node card_t = nm->mkNode(kind::CARD, t);
//         Node card_sNt = nm->mkNode(kind::CARD, sNt);
//         Node card_sMt = nm->mkNode(kind::CARD, sMt);
//         Node card_tMs = nm->mkNode(kind::CARD, tMs);

//         Node lem;
      
//         // for s
//         lem = nm->mkNode(kind::EQUAL,
//                          card_s,
//                          nm->mkNode(kind::PLUS, card_sNt, card_sMt));
//         d_external.d_out->lemma(lem);

//         // for t
//         lem = nm->mkNode(kind::EQUAL,
//                          card_t,
//                          nm->mkNode(kind::PLUS, card_sNt, card_tMs));

//         d_external.d_out->lemma(lem);

//         // for union
//         if(isUnion) {
//           lem = nm->mkNode(kind::EQUAL,
//                            n,     // card(s union t)
//                            nm->mkNode(kind::PLUS, card_sNt, card_sMt, card_tMs));
//           d_external.d_out->lemma(lem);
//         }
      
//         d_processedCardPairs.insert(make_pair(make_pair(s, t), isUnion));

//       } else if(isUnion && processedInfo->second == false) {
      
//         Node sNt = nm->mkNode(kind::INTERSECTION, s, t);
//         sNt = Rewriter::rewrite(sNt);
//         Node sMt = nm->mkNode(kind::SETMINUS, s, t);
//         sMt = Rewriter::rewrite(sMt);
//         Node tMs = nm->mkNode(kind::SETMINUS, t, s);
//         tMs = Rewriter::rewrite(tMs);

//         Node card_s = nm->mkNode(kind::CARD, s);
//         Node card_t = nm->mkNode(kind::CARD, t);
//         Node card_sNt = nm->mkNode(kind::CARD, sNt);
//         Node card_sMt = nm->mkNode(kind::CARD, sMt);
//         Node card_tMs = nm->mkNode(kind::CARD, tMs);

//         Assert(Rewriter::rewrite(n[0]) == n[0]);

//         Node lem = nm->mkNode(kind::EQUAL,
//                               n,     // card(s union t)
//                               nm->mkNode(kind::PLUS, card_sNt, card_sMt, card_tMs));
//         d_external.d_out->lemma(lem);

//         processedInfo->second = true;
//       }
    
//     }//equivalence class loop

//   }//d_cardTerms loop

//   if(newLemmaGenerated) {
//     Trace("sets-card") << "[sets-card] New introduce done. Returning." << std::endl;
//     return;
//   }



//   // Leaves disjoint lemmas
//   buildGraph();

//   // Leaves disjoint lemmas
//   for(typeof(leaves.begin()) it = leaves.begin(); it != leaves.end(); ++it) {
//     TNode l1 = (*it);
//     if(d_equalityEngine.getRepresentative(l1).getKind() == kind::EMPTYSET) continue;
//     for(typeof(leaves.begin()) jt = leaves.begin(); jt != leaves.end(); ++jt) {
//       TNode l2 = (*jt);

//       if(d_equalityEngine.getRepresentative(l2).getKind() == kind::EMPTYSET) continue;

//       if( l1 == l2 ) continue;

//       Node l1_inter_l2 = nm->mkNode(kind::INTERSECTION, min(l1, l2), max(l1, l2));
//       l1_inter_l2 = Rewriter::rewrite(l1_inter_l2);
//       Node emptySet = nm->mkConst<EmptySet>(EmptySet(nm->toType(l1_inter_l2.getType())));
//       if(d_equalityEngine.hasTerm(l1_inter_l2) &&
//          d_equalityEngine.hasTerm(emptySet) &&
//          d_equalityEngine.areEqual(l1_inter_l2, emptySet)) {
//         Debug("sets-card-graph") << "[sets-card-graph] Disjoint (asserted): " << l1 << " and " << l2 << std::endl;
//         continue;               // known to be disjoint
//       }

//       std::set<TNode> l1_ancestors = getReachable(edgesBk, l1);
//       std::set<TNode> l2_ancestors = getReachable(edgesBk, l2);

//       // have a disjoint edge
//       bool loop = true;
//       bool equality = false;
//       for(typeof(l1_ancestors.begin()) l1_it = l1_ancestors.begin();
//           l1_it != l1_ancestors.end() && loop; ++l1_it) {
//         for(typeof(l2_ancestors.begin()) l2_it = l2_ancestors.begin();
//             l2_it != l2_ancestors.end() && loop; ++l2_it) {
//           TNode n1 = (*l1_it);
//           TNode n2 = (*l2_it);
//           if(disjoint.find(make_pair(n1, n2)) != disjoint.find(make_pair(n2, n1))) {
//             loop = false;
//           }
//           if(n1 == n2) {
//             equality = true;
//           }
//           if(d_equalityEngine.hasTerm(n1) && d_equalityEngine.hasTerm(n2) &&
//              d_equalityEngine.areEqual(n1, n2)) {
//             equality = true;
//           }
//         }
//       }
//       if(loop == false) {
//         Debug("sets-card-graph") << "[sets-card-graph] Disjoint (always): " << l1 << " and " << l2 << std::endl;
//         continue;
//       }
//       if(equality == false) {
//         Debug("sets-card-graph") << "[sets-card-graph] No equality found: " << l1 << " and " << l2 << std::endl;
//         continue;
//       }

//       Node lem = nm->mkNode(kind::OR,
//                             nm->mkNode(kind::EQUAL, l1_inter_l2, emptySet),
//                             nm->mkNode(kind::LT, nm->mkConst(Rational(0)),
//                                        nm->mkNode(kind::CARD, l1_inter_l2)));

//       d_external.d_out->lemma(lem);
//       Trace("sets-card") << "[sets-card] Guessing disjointness of : " << l1 << " and " << l2 << std::endl;
//       if(Debug.isOn("sets-card-disjoint")) {
//         Debug("sets-card-disjoint") << "[sets-card-disjoint] Lemma for " << l1 << " and " << l2 << " generated because:" << std::endl;
//         for(typeof(disjoint.begin()) it = disjoint.begin(); it != disjoint.end(); ++it) {
//           Debug("sets-card-disjoint") << "[sets-card-disjoint]   " << it->first << " " << it->second << std::endl;
//         }
//       }
//       newLemmaGenerated = true;
//       Trace("sets-card") << "[sets-card] New intersection being empty lemma generated. Returning." << std::endl;
//       return;
//     }
//   }

//   Assert(!newLemmaGenerated);



//   // Elements being either equal or disequal
  
//   for(typeof(leaves.begin()) it = leaves.begin();
//       it != leaves.end(); ++it) {
//     Assert(d_equalityEngine.hasTerm(*it));
//     Node n = d_equalityEngine.getRepresentative(*it);
//     Assert(n.getKind() == kind::EMPTYSET || leaves.find(n) != leaves.end());
//     if(n != *it) continue;
//     const CDTNodeList* l = d_termInfoManager->getMembers(*it);
//     std::set<TNode> elems;
//     for(typeof(l->begin()) l_it = l->begin(); l_it != l->end(); ++l_it) {
//       elems.insert(d_equalityEngine.getRepresentative(*l_it));
//     }
//     for(typeof(elems.begin()) e1_it = elems.begin(); e1_it != elems.end(); ++e1_it) {
//       for(typeof(elems.begin()) e2_it = elems.begin(); e2_it != elems.end(); ++e2_it) {
//         if(*e1_it == *e2_it) continue;
//         if(!d_equalityEngine.areDisequal(*e1_it, *e2_it, false)) {
//           Node lem = nm->mkNode(kind::EQUAL, *e1_it, *e2_it);
//           lem = nm->mkNode(kind::OR, lem, nm->mkNode(kind::NOT, lem));
//           d_external.d_out->lemma(lem);
//           newLemmaGenerated = true;
//         }
//       }
//     }
//   }

//   if(newLemmaGenerated) {
//     Trace("sets-card") << "[sets-card] Members arrangments lemmas. Returning." << std::endl;
//     return;
//   }


//   // Guess leaf nodes being empty or non-empty
//   for(typeof(leaves.begin()) it = leaves.begin(); it != leaves.end(); ++it) {
//     Node n = d_equalityEngine.getRepresentative(*it);
//     if(n.getKind() == kind::EMPTYSET) continue;
//     if(d_termInfoManager->getMembers(n)->size() > 0) continue;
//     Node emptySet = nm->mkConst<EmptySet>(EmptySet(nm->toType(n.getType())));
//     if(!d_equalityEngine.hasTerm(emptySet)) {
//       d_equalityEngine.addTerm(emptySet);
//     }
//     if(!d_equalityEngine.areDisequal(n, emptySet, false)) {
//       Node lem = nm->mkNode(kind::EQUAL, n, emptySet);
//       lem = nm->mkNode(kind::OR, lem, nm->mkNode(kind::NOT, lem));
//       Assert(d_cardLowerLemmaCache.find(lem) == d_cardLowerLemmaCache.end());
//       d_cardLowerLemmaCache.insert(lem);
//       d_external.d_out->lemma(lem);
//       newLemmaGenerated = true;
//       break;
//     }
//   }

//   if(newLemmaGenerated) {
//     Trace("sets-card") << "[sets-card] New guessing leaves being empty done." << std::endl;
//     return;
//   }

//   // Assert Lower bound
//   for(typeof(leaves.begin()) it = leaves.begin();
//       it != leaves.end(); ++it) {
//     Assert(d_equalityEngine.hasTerm(*it));
//     Node n = d_equalityEngine.getRepresentative(*it);
//     Assert(n.getKind() == kind::EMPTYSET || leaves.find(n) != leaves.end());
//     if(n != *it) continue;
//     const CDTNodeList* l = d_termInfoManager->getMembers(n);
//     std::set<TNode> elems;
//     for(typeof(l->begin()) l_it = l->begin(); l_it != l->end(); ++l_it) {
//       elems.insert(d_equalityEngine.getRepresentative(*l_it));
//     }
//     if(elems.size() == 0) continue;
//     NodeBuilder<> nb(kind::OR);
//     nb << ( nm->mkNode(kind::LEQ, nm->mkConst(Rational(elems.size())), nm->mkNode(kind::CARD, n)) );
//     if(elems.size() > 1) {
//       for(typeof(elems.begin()) e1_it = elems.begin(); e1_it != elems.end(); ++e1_it) {
//         for(typeof(elems.begin()) e2_it = elems.begin(); e2_it != elems.end(); ++e2_it) {
//           if(*e1_it == *e2_it) continue;
//           nb << (nm->mkNode(kind::EQUAL, *e1_it, *e2_it));
//         }
//       }
//     }
//     for(typeof(elems.begin()) e_it = elems.begin(); e_it != elems.end(); ++e_it) {
//       nb << nm->mkNode(kind::NOT, nm->mkNode(kind::MEMBER, *e_it, n));
//     }
//     Node lem = Node(nb);
//     if(d_cardLowerLemmaCache.find(lem) == d_cardLowerLemmaCache.end()) {
//       Trace("sets-card") << "[sets-card] Card Lower: " << lem << std::endl;
//       d_external.d_out->lemma(lem);
//       d_cardLowerLemmaCache.insert(lem);
//       newLemmaGenerated = true;
//     }
//   }  
// }

