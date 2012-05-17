/*********************                                                        */
/*! \file tableau.cpp
 ** \verbatim
 ** Original author: taking
 ** Major contributors: none
 ** Minor contributors (to current version): mdeters
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/


#include "theory/arith/matrix.h"

using namespace std;
namespace CVC4 {
namespace theory {
namespace arith {


/*
void Tableau::addRow(ArithVar basicVar,
                     const std::vector<Rational>& coeffs,
                     const std::vector<ArithVar>& variables){

  Assert(coeffs.size() == variables.size());

  //The new basic variable cannot already be a basic variable
  Assert(!d_basicVariables.isMember(basicVar));
  d_basicVariables.add(basicVar);
  ReducedRowVector* row_current = new ReducedRowVector(basicVar,variables, coeffs,d_rowCount, d_columnMatrix);
  d_rowsTable[basicVar] = row_current;

  //A variable in the row may have been made non-basic already.
  //If this is the case we fake pivoting this variable
  vector<ArithVar>::const_iterator varsIter = variables.begin();
  vector<ArithVar>::const_iterator varsEnd = variables.end();

  for( ; varsIter != varsEnd; ++varsIter){
    ArithVar var = *varsIter;

    if(d_basicVariables.isMember(var)){
      EntryID varID = find(basicVar, var);
      TableauEntry& entry = d_entryManager.get(varID);
      const Rational& coeff = entry.getCoefficient();

      loadRowIntoMergeBuffer(var);
      rowPlusRowTimesConstant(coeff, basicVar, var);
      emptyRowFromMergeBuffer(var);
    }
  }
}
*/

/*
ReducedRowVector* Tableau::removeRow(ArithVar basic){
  Assert(isBasic(basic));

  ReducedRowVector* row = d_rowsTable[basic];

  d_basicVariables.remove(basic);
  d_rowsTable[basic] = NULL;

  return row;
}
*/

void Tableau::pivot(ArithVar oldBasic, ArithVar newBasic){
  Assert(isBasic(oldBasic));
  Assert(!isBasic(newBasic));
  Assert(d_mergeBuffer.empty());

  Debug("tableau") << "Tableau::pivot(" <<  oldBasic <<", " << newBasic <<")"  << endl;

  RowIndex ridx = basicToRowIndex(oldBasic);

  rowPivot(oldBasic, newBasic);
  Assert(ridx == basicToRowIndex(newBasic));

  loadRowIntoBuffer(ridx);

  ColIterator colIter = colIterator(newBasic);
  while(!colIter.atEnd()){
    EntryID id = colIter.getID();
    Entry& entry = d_entries.get(id);

    ++colIter; //needs to be incremented before the variable is removed
    if(entry.getRowIndex() == ridx){ continue; }

    RowIndex to = entry.getRowIndex();
    Rational coeff = entry.getCoefficient();

    rowPlusBufferTimesConstant(to, coeff);
  }
  clearBuffer();

  //Clear the column for used for this variable

  Assert(d_mergeBuffer.empty());
  Assert(!isBasic(oldBasic));
  Assert(isBasic(newBasic));
  Assert(getColLength(newBasic) == 1);
}

// void Tableau::printTableau() const {
//   Debug("tableau") << "Tableau::d_activeRows"  << endl;

//   ArithVarSet::const_iterator basicIter = beginBasic(), endIter = endBasic();
//   for(; basicIter != endIter; ++basicIter){
//     ArithVar basic = *basicIter;
//     printRow(basic);
//   }
// }

// void Tableau::printRow(ArithVar basic) const {
//   Debug("tableau") << "{" << basic << ":";
//   for(RowIterator entryIter = rowIterator(basic); !entryIter.atEnd(); ++entryIter){
//     const TableauEntry& entry = *entryIter;
//     printEntry(entry);
//     Debug("tableau") << ",";
//   }
//   Debug("tableau") << "}" << endl;
// }

// void Tableau::printEntry(const TableauEntry& entry) const {
//   Debug("tableau") << entry.getColVar() << "*" << entry.getCoefficient();
// }

// uint32_t Tableau::numNonZeroEntriesByRow() const {
//   uint32_t rowSum = 0;
//   ArithVarSet::const_iterator i = d_basicVariables.begin(), end = d_basicVariables.end();
//   for(; i != end; ++i){
//     ArithVar basic = *i;
//     rowSum += getRowLength(basic);
//   }
//   return rowSum;
// }

// uint32_t Tableau::numNonZeroEntriesByCol() const {
//   uint32_t colSum = 0;
//   VectorSizeTable::const_iterator i = d_colLengths.begin();
//   VectorSizeTable::const_iterator end = d_colLengths.end();
//   for(; i != end; ++i){
//     colSum += *i;
//   }
//   return colSum;
// }


// EntryID Tableau::findOnRow(ArithVar row, ArithVar col){
//   for(RowIterator i = rowIterator(row); !i.atEnd(); ++i){
//     EntryID id = i.getID();
//     const TableauEntry& entry = *i;
//     ArithVar colVar = entry.getColVar();

//     if(colVar == col){
//       return id;
//     }
//   }
//   return ENTRYID_SENTINEL;
// }

// EntryID Tableau::findOnCol(ArithVar row, ArithVar col){
//   for(ColIterator i = colIterator(col); !i.atEnd(); ++i){
//     EntryID id = i.getID();
//     const TableauEntry& entry = *i;
//     ArithVar rowVar = entry.getRowVar();

//     if(rowVar == row){
//       return id;
//     }
//   }
//   return ENTRYID_SENTINEL;
// }

// const TableauEntry& Tableau::findEntry(ArithVar row, ArithVar col){
//   bool colIsShorter = getColLength(col) < getRowLength(row);
//   EntryID id = colIsShorter ? findOnCol(row,col) : findOnRow(row,col);
//   if(id == ENTRYID_SENTINEL){
//     return d_failedFind;
//   }else{
//     return d_entryManager.get(id);
//   }
// }

// void Tableau::removeRow(ArithVar basic){
//   RowIterator i = rowIterator(basic);
//   while(!i.atEnd()){
//     EntryID id = i.getID();
//     ++i;
//     removeEntry(id);
//   }
//   d_basicVariables.remove(basic);
// }

// void Tableau::loadRowIntoMergeBuffer(ArithVar basic){
//   Assert(mergeBufferIsEmpty());
//   for(RowIterator i = rowIterator(basic); !i.atEnd(); ++i){
//     EntryID id = i.getID();
//     const TableauEntry& entry = *i;
//     ArithVar colVar = entry.getColVar();
//     d_mergeBuffer[colVar] = make_pair(id, false);
//   }
// }

// void Tableau::emptyRowFromMergeBuffer(ArithVar basic){
//   Assert(isBasic(basic));
//   for(RowIterator i = rowIterator(basic); !i.atEnd(); ++i){
//     const TableauEntry& entry = *i;
//     ArithVar colVar = entry.getColVar();
//     Assert(d_mergeBuffer[colVar].first == i.getID());
//     d_mergeBuffer[colVar] = make_pair(ENTRYID_SENTINEL, false);
//   }

//   Assert(mergeBufferIsEmpty());
// }


/**
 * Changes basic to newbasic (a variable on the row).
 */
void Tableau::rowPivot(ArithVar basicOld, ArithVar basicNew){
  Assert(isBasic(basicOld));
  Assert(!isBasic(basicNew));

  RowIndex rid = basicToRowIndex(basicOld);

  EntryID newBasicID = findOnRow(rid, basicNew);

  Assert(newBasicID != ENTRYID_SENTINEL);

  Tableau::Entry& newBasicEntry = d_entries.get(newBasicID);
  Rational negInverseA_rs = -(newBasicEntry.getCoefficient().inverse());

  for(RowIterator i = basicRowIterator(basicOld); !i.atEnd(); ++i){
    EntryID id = i.getID();
    Tableau::Entry& entry = d_entries.get(id);

    entry.getCoefficient() *=  negInverseA_rs;
  }

  d_basic2RowIndex.remove(basicOld);
  d_basic2RowIndex.set(basicNew, rid);
  d_rowIndex2basic[rid] = basicNew;
}

// void Tableau::addEntry(ArithVar row, ArithVar col, const Rational& coeff){
//   Assert(coeff != 0);

//   EntryID newId = d_entryManager.newEntry();
//   TableauEntry& newEntry =  d_entryManager.get(newId);
//   newEntry = TableauEntry( row, col,
//                            d_rowHeads[row], d_colHeads[col],
//                            ENTRYID_SENTINEL, ENTRYID_SENTINEL,
//                            coeff);
//   Assert(newEntry.getCoefficient() != 0);

//   Debug("tableau") << "addEntry(" << row << "," << col <<"," << coeff << ")" << endl;

//   ++d_entriesInUse;

//   if(d_rowHeads[row] != ENTRYID_SENTINEL)
//     d_entryManager.get(d_rowHeads[row]).setPrevRowID(newId);

//   if(d_colHeads[col] != ENTRYID_SENTINEL)
//     d_entryManager.get(d_colHeads[col]).setPrevColID(newId);

//   d_rowHeads[row] = newId;
//   d_colHeads[col] = newId;
//   ++d_rowLengths[row];
//   ++d_colLengths[col];
// }

// void Tableau::removeEntry(EntryID id){
//   Assert(d_entriesInUse > 0);
//   --d_entriesInUse;

//   TableauEntry& entry = d_entryManager.get(id);

//   ArithVar row = entry.getRowVar();
//   ArithVar col = entry.getColVar();

//   Assert(d_rowLengths[row] > 0);
//   Assert(d_colLengths[col] > 0);


//   --d_rowLengths[row];
//   --d_colLengths[col];

//   EntryID prevRow = entry.getPrevRowID();
//   EntryID prevCol = entry.getPrevColID();

//   EntryID nextRow = entry.getNextRowID();
//   EntryID nextCol = entry.getNextColID();

//   if(d_rowHeads[row] == id){
//     d_rowHeads[row] = nextRow;
//   }
//   if(d_colHeads[col] == id){
//     d_colHeads[col] = nextCol;
//   }

//   entry.markBlank();

//   if(prevRow != ENTRYID_SENTINEL){
//     d_entryManager.get(prevRow).setNextRowID(nextRow);
//   }
//   if(nextRow != ENTRYID_SENTINEL){
//     d_entryManager.get(nextRow).setPrevRowID(prevRow);
//   }

//   if(prevCol != ENTRYID_SENTINEL){
//     d_entryManager.get(prevCol).setNextColID(nextCol);
//   }
//   if(nextCol != ENTRYID_SENTINEL){
//     d_entryManager.get(nextCol).setPrevColID(prevCol);
//   }

//   d_entryManager.freeEntry(id);
// }

// void Tableau::rowPlusRowTimesConstant(ArithVar basicTo, const Rational& c, ArithVar basicFrom){

//   Debug("tableau") << "rowPlusRowTimesConstant("
//                    << basicTo << "," << c << "," << basicFrom << ")"
//                    << endl;

//   Assert(debugNoZeroCoefficients(basicTo));
//   Assert(debugNoZeroCoefficients(basicFrom));

//   Assert(c != 0);
//   Assert(isBasic(basicTo));
//   Assert(isBasic(basicFrom));
//   Assert( d_usedList.empty() );


//   RowIterator i = rowIterator(basicTo);
//   while(!i.atEnd()){
//     EntryID id = i.getID();
//     TableauEntry& entry = d_entryManager.get(id);
//     ArithVar colVar = entry.getColVar();

//     ++i;
//     if(bufferPairIsNotEmpty(d_mergeBuffer[colVar])){
//       d_mergeBuffer[colVar].second = true;
//       d_usedList.push_back(colVar);

//       EntryID inOtherRow = d_mergeBuffer[colVar].first;
//       const TableauEntry& other = d_entryManager.get(inOtherRow);
//       entry.getCoefficient() += c * other.getCoefficient();

//       if(entry.getCoefficient().sgn() == 0){
//         removeEntry(id);
//       }
//     }
//   }

//   for(RowIterator i = rowIterator(basicFrom); !i.atEnd(); ++i){
//     const TableauEntry& entry = *i;
//     ArithVar colVar = entry.getColVar();

//     if(!(d_mergeBuffer[colVar]).second){
//       Rational newCoeff =  c * entry.getCoefficient();
//       addEntry(basicTo, colVar, newCoeff);
//     }
//   }

//   clearUsedList();

//   if(Debug.isOn("tableau")) { printTableau(); }
// }

// void Tableau::clearUsedList(){
//   ArithVarArray::iterator i, end;
//   for(i = d_usedList.begin(), end = d_usedList.end(); i != end; ++i){
//     ArithVar pos = *i;
//     d_mergeBuffer[pos].second = false;
//   }
//   d_usedList.clear();
// }

void Tableau::addRow(ArithVar basic,
                     const std::vector<Rational>& coefficients,
                     const std::vector<ArithVar>& variables)
{
  Assert(basic < getNumColumns());

  Assert(coefficients.size() == variables.size() );
  Assert(!isBasic(basic));

  RowIndex newRow = Matrix<Rational>::addRow(coefficients, variables);
  addEntry(newRow, basic, Rational(-1));

  Assert(d_rowIndex2basic.size() == newRow);

  d_basic2RowIndex.set(basic, newRow);
  d_rowIndex2basic.push_back(basic);


  if(Debug.isOn("matrix")){ printMatrix(); }

  vector<Rational>::const_iterator coeffIter = coefficients.begin();
  vector<ArithVar>::const_iterator varsIter = variables.begin();
  vector<ArithVar>::const_iterator varsEnd = variables.end();
  for(; varsIter != varsEnd; ++coeffIter, ++varsIter){
    ArithVar var = *varsIter;

    if(isBasic(var)){
      Rational coeff = *coeffIter;

      RowIndex ri = basicToRowIndex(var);

      loadRowIntoBuffer(ri);
      rowPlusBufferTimesConstant(newRow, coeff);
      clearBuffer();
    }
  }

  if(Debug.isOn("matrix")) { printMatrix(); }

  Assert(debugNoZeroCoefficients(newRow));
  Assert(debugMatchingCountsForRow(newRow));
  Assert(getColLength(basic) == 1);
}

// bool Tableau::debugNoZeroCoefficients(ArithVar basic){
//   for(RowIterator i=rowIterator(basic); !i.atEnd(); ++i){
//     const TableauEntry& entry = *i;
//     if(entry.getCoefficient() == 0){
//       return false;
//     }
//   }
//   return true;
// }
// bool Tableau::debugMatchingCountsForRow(ArithVar basic){
//   for(RowIterator i=rowIterator(basic); !i.atEnd(); ++i){
//     const TableauEntry& entry = *i;
//     ArithVar colVar = entry.getColVar();
//     uint32_t count = debugCountColLength(colVar);
//     Debug("tableau") << "debugMatchingCountsForRow "
//                      << basic << ":" << colVar << " " << count
//                      <<" "<< d_colLengths[colVar] << endl;
//     if( count != d_colLengths[colVar] ){
//       return false;
//     }
//   }
//   return true;
// }


// uint32_t Tableau::debugCountColLength(ArithVar var){
//   Debug("tableau") << var << " ";
//   uint32_t count = 0;
//   for(ColIterator i=colIterator(var); !i.atEnd(); ++i){
//     const TableauEntry& entry = *i;
//     Debug("tableau") << "(" << entry.getRowVar() << ", " << i.getID() << ") ";
//     ++count;
//   }
//   Debug("tableau") << endl;
//   return count;
// }

// uint32_t Tableau::debugCountRowLength(ArithVar var){
//   uint32_t count = 0;
//   for(RowIterator i=rowIterator(var); !i.atEnd(); ++i){
//     ++count;
//   }
//   return count;
// }

/*
void ReducedRowVector::enqueueNonBasicVariablesAndCoefficients(std::vector< ArithVar >& variables,std::vector< Rational >& coefficients) const{
  for(const_iterator i=begin(), endEntries=end(); i != endEntries; ++i){
    ArithVar var = (*i).getArithVar();
    const Rational& q = (*i).getCoefficient();
    if(var != basic()){
      variables.push_back(var);
      coefficients.push_back(q);
    }
  }
  }*/

// Node Tableau::rowAsEquality(ArithVar basic, const ArithVarToNodeMap& map){
//   using namespace CVC4::kind;

//   Assert(getRowLength(basic) >= 2);

//   vector<Node> nonBasicPairs;
//   for(RowIterator i = rowIterator(basic); !i.atEnd(); ++i){
//     const TableauEntry& entry = *i;
//     ArithVar colVar = entry.getColVar();
//     if(colVar == basic) continue;
//     Node var = (map.find(colVar))->second;
//     Node coeff = mkRationalNode(entry.getCoefficient());

//     Node mult = NodeBuilder<2>(MULT) << coeff << var;
//     nonBasicPairs.push_back(mult);
//   }

//   Node sum = Node::null();
//   if(nonBasicPairs.size() == 1 ){
//     sum = nonBasicPairs.front();
//   }else{
//     Assert(nonBasicPairs.size() >= 2);
//     NodeBuilder<> sumBuilder(PLUS);
//     sumBuilder.append(nonBasicPairs);
//     sum = sumBuilder;
//   }
//   Node basicVar = (map.find(basic))->second;
//   return NodeBuilder<2>(EQUAL) << basicVar << sum;
// }

// double Tableau::densityMeasure() const{
//   Assert(numNonZeroEntriesByRow() == numNonZeroEntries());
//   Assert(numNonZeroEntriesByCol() == numNonZeroEntries());

//   uint32_t n = getNumRows();
//   if(n == 0){
//     return 1.0;
//   }else {
//     uint32_t s = numNonZeroEntries();
//     uint32_t m = d_colHeads.size();
//     uint32_t divisor = (n *(m - n + 1));

//     Assert(n >= 1);
//     Assert(m >= n);
//     Assert(divisor > 0);
//     Assert(divisor >= s);

//     return (double(s)) / divisor;
//   }
// }

// void TableauEntryManager::freeEntry(EntryID id){
//   Assert(get(id).blank());
//   Assert(d_size > 0);

//   d_freedEntries.push(id);
//   --d_size;
// }

// EntryID TableauEntryManager::newEntry(){
//   EntryID newId;
//   if(d_freedEntries.empty()){
//     newId = d_entries.size();
//     d_entries.push_back(TableauEntry());
//   }else{
//     newId = d_freedEntries.front();
//     d_freedEntries.pop();
//   }
//   ++d_size;
//   return newId;
// }


}/* CVC4::theory::arith namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */
