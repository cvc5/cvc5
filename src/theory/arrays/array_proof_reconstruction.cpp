/*********************                                                        */
/*! \file array_proof_reconstruction.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Guy Katz
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** [[ Add lengthier description here ]]

 ** \todo document this file

**/

#include "theory/arrays/array_proof_reconstruction.h"

namespace CVC4 {
namespace theory {
namespace arrays {

ArrayProofReconstruction::ArrayProofReconstruction(const eq::EqualityEngine* equalityEngine)
  : d_equalityEngine(equalityEngine) {
}

void ArrayProofReconstruction::setRowMergeTag(unsigned tag) {
  d_reasonRow = tag;
}

void ArrayProofReconstruction::setRow1MergeTag(unsigned tag) {
  d_reasonRow1 = tag;
}

void ArrayProofReconstruction::setExtMergeTag(unsigned tag) {
  d_reasonExt = tag;
}

void ArrayProofReconstruction::notify(unsigned reasonType, Node reason, Node a, Node b,
                                      std::vector<TNode>& equalities, eq::EqProof* proof) const {

  Debug("pf::array") << "ArrayProofReconstruction::notify( "
                     << reason << ", " << a << ", " << b << std::endl;


  if (reasonType == d_reasonExt) {
    if (proof) {
      // Todo: here we assume that a=b is an assertion. We should probably call explain()
      // recursively, to explain this.
      eq::EqProof* childProof = new eq::EqProof;
      childProof->d_node = reason;
      proof->d_children.push_back(childProof);
    }
  }

  else if (reasonType == d_reasonRow) {
    // ROW rules mean that (i==k) OR ((a[i]:=t)[k] == a[k])
    // The equality here will be either (i == k) because ((a[i]:=t)[k] != a[k]),
    // or ((a[i]:=t)[k] == a[k]) because (i != k).

    if (proof) {
      if (a.getKind() == kind::SELECT) {
        // This is the case of ((a[i]:=t)[k] == a[k]) because (i != k).

        // The edge is ((a[i]:=t)[k], a[k]), or (a[k], (a[i]:=t)[k]). This flag should be
        // false in the first case and true in the second case.
        bool currentNodeIsUnchangedArray;

        Assert(a.getNumChildren() == 2);
        Assert(b.getNumChildren() == 2);

        if (a[0].getKind() == kind::VARIABLE || a[0].getKind() == kind::SKOLEM) {
          currentNodeIsUnchangedArray = true;
        } else if (b[0].getKind() == kind::VARIABLE || b[0].getKind() == kind::SKOLEM) {
          currentNodeIsUnchangedArray = false;
        } else {
          Assert(a[0].getKind() == kind::STORE);
          Assert(b[0].getKind() == kind::STORE);

          if (a[0][0] == b[0]) {
            currentNodeIsUnchangedArray = false;
          } else if (b[0][0] == a[0]) {
            currentNodeIsUnchangedArray = true;
          } else {
            Unreachable();
          }
        }

        Node indexOne = currentNodeIsUnchangedArray ? a[1] : a[0][1];
        Node indexTwo = currentNodeIsUnchangedArray ? b[0][1] : b[1];

        // Some assertions to ensure that the theory of arrays behaves as expected
        Assert(a[1] == b[1]);
        if (currentNodeIsUnchangedArray) {
          Assert(a[0] == b[0][0]);
        } else {
          Assert(a[0][0] == b[0]);
        }

        Debug("pf::ee") << "Getting explanation for ROW guard: "
                        << indexOne << " != " << indexTwo << std::endl;


        eq::EqProof* childProof = new eq::EqProof;
        d_equalityEngine->explainEquality(indexOne, indexTwo, false, equalities, childProof);

        // It could be that the guard condition is a constant disequality. In this case,
        // we need to change it to a different format.
        bool haveNegChild = false;
        for (unsigned i = 0; i < childProof->d_children.size(); ++i) {
          if (childProof->d_children[i]->d_node.getKind() == kind::NOT)
            haveNegChild = true;
        }

        if ((childProof->d_children.size() != 0) &&
            (childProof->d_id == theory::eq::MERGED_THROUGH_CONSTANTS || !haveNegChild)) {
          // The proof has two children, explaining why each index is a (different) constant.
          Assert(childProof->d_children.size() == 2);

          Node constantOne, constantTwo;
          // Each subproof explains why one of the indices is constant.

          if (childProof->d_children[0]->d_id == theory::eq::MERGED_THROUGH_REFLEXIVITY) {
            constantOne = childProof->d_children[0]->d_node;
          } else {
            Assert(childProof->d_children[0]->d_node.getKind() == kind::EQUAL);
            if ((childProof->d_children[0]->d_node[0] == indexOne) ||
                (childProof->d_children[0]->d_node[0] == indexTwo)) {
              constantOne = childProof->d_children[0]->d_node[1];
            } else {
              constantOne = childProof->d_children[0]->d_node[0];
            }
          }

          if (childProof->d_children[1]->d_id == theory::eq::MERGED_THROUGH_REFLEXIVITY) {
            constantTwo = childProof->d_children[1]->d_node;
          } else {
            Assert(childProof->d_children[1]->d_node.getKind() == kind::EQUAL);
            if ((childProof->d_children[1]->d_node[0] == indexOne) ||
                (childProof->d_children[1]->d_node[0] == indexTwo)) {
              constantTwo = childProof->d_children[1]->d_node[1];
            } else {
              constantTwo = childProof->d_children[1]->d_node[0];
            }
          }

          eq::EqProof* constantDisequalityProof = new eq::EqProof;
          constantDisequalityProof->d_id = theory::eq::MERGED_THROUGH_CONSTANTS;
          constantDisequalityProof->d_node =
            NodeManager::currentNM()->mkNode(kind::EQUAL, constantOne, constantTwo).negate();

          // Middle is where we need to insert the new disequality
          std::vector<eq::EqProof *>::iterator middle = childProof->d_children.begin();
          ++middle;

          childProof->d_children.insert(middle, constantDisequalityProof);

          childProof->d_id = theory::eq::MERGED_THROUGH_TRANS;
          childProof->d_node =
            NodeManager::currentNM()->mkNode(kind::EQUAL, indexOne, indexTwo).negate();
        }

        proof->d_children.push_back(childProof);
      } else {
        // This is the case of (i == k) because ((a[i]:=t)[k] != a[k]),

        Node indexOne = a;
        Node indexTwo = b;

        Debug("pf::ee") << "The two indices are: " << indexOne << ", " << indexTwo << std::endl
                        << "The reason for the edge is: " << reason << std::endl;

        Assert(reason.getNumChildren() == 2);
        Debug("pf::ee") << "Getting explanation for ROW guard: " << reason[1] << std::endl;

        eq::EqProof* childProof = new eq::EqProof;
        d_equalityEngine->explainEquality(reason[1][0], reason[1][1], false, equalities, childProof);
        proof->d_children.push_back(childProof);
      }
    }

  }

  else if (reasonType == d_reasonRow1) {
    // No special handling required at this time
  }
}

}/* CVC4::theory::arrays namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */
