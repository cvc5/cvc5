/*********************                                                        */
/*! \file matrix.h
 ** \verbatim
 ** Original author: Tim King
 ** Major contributors: none
 ** Minor contributors (to current version): Morgan Deters
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Sparse matrix implementations for different types.
 **
 ** Sparse matrix implementations for different types.
 ** This defines Matrix<T>, IntegerEqualityTables and Tableau.
 **/

#include "cvc4_private.h"

#pragma once

#include "expr/node.h"

#include "util/index.h"
#include "util/dense_map.h"

#include "theory/arith/arithvar.h"
#include "theory/arith/arithvar_node_map.h"
#include "theory/arith/normal_form.h"

#include <queue>
#include <vector>
#include <utility>

namespace CVC4 {
namespace theory {
namespace arith {

typedef Index EntryID;
const EntryID ENTRYID_SENTINEL = std::numeric_limits<EntryID>::max();

typedef Index RowIndex;
const RowIndex ROW_INDEX_SENTINEL  = std::numeric_limits<RowIndex>::max();

template<class T>
class MatrixEntry {
private:
  RowIndex d_rowIndex;
  ArithVar d_colVar;

  EntryID d_nextRow;
  EntryID d_nextCol;

  EntryID d_prevRow;
  EntryID d_prevCol;

  T d_coefficient;

public:
  MatrixEntry():
    d_rowIndex(ROW_INDEX_SENTINEL),
    d_colVar(ARITHVAR_SENTINEL),
    d_nextRow(ENTRYID_SENTINEL),
    d_nextCol(ENTRYID_SENTINEL),
    d_prevRow(ENTRYID_SENTINEL),
    d_prevCol(ENTRYID_SENTINEL),
    d_coefficient()
  {}

  MatrixEntry(RowIndex row, ArithVar col, const T& coeff):
     d_rowIndex(row),
     d_colVar(col),
     d_nextRow(ENTRYID_SENTINEL),
     d_nextCol(ENTRYID_SENTINEL),
     d_prevRow(ENTRYID_SENTINEL),
     d_prevCol(ENTRYID_SENTINEL),
     d_coefficient(coeff)
  {}

private:
  bool unusedConsistent() const {
    return
      (d_rowIndex == ROW_INDEX_SENTINEL && d_colVar == ARITHVAR_SENTINEL) ||
      (d_rowIndex != ROW_INDEX_SENTINEL && d_colVar != ARITHVAR_SENTINEL);
  }

public:

  EntryID getNextRowEntryID() const {
    return d_nextRow;
  }

  EntryID getNextColEntryID() const {
    return d_nextCol;
  }
  EntryID getPrevRowEntryID() const {
    return d_prevRow;
  }

  EntryID getPrevColEntryID() const {
    return d_prevCol;
  }

  void setNextRowEntryID(EntryID id) {
    d_nextRow = id;
  }
  void setNextColEntryID(EntryID id) {
    d_nextCol = id;
  }
  void setPrevRowEntryID(EntryID id) {
    d_prevRow = id;
  }
  void setPrevColEntryID(EntryID id) {
    d_prevCol = id;
  }

  RowIndex getRowIndex() const{
    return d_rowIndex;
  }

  ArithVar getColVar() const{
    return d_colVar;
  }

  const T& getCoefficient() const {
    return d_coefficient;
  }

  T& getCoefficient(){
    return d_coefficient;
  }

  void setCoefficient(const T& t){
    d_coefficient = t;
  }

  void markBlank() {
    d_rowIndex = ROW_INDEX_SENTINEL;
    d_colVar = ARITHVAR_SENTINEL;
  }

  bool blank() const{
    Assert(unusedConsistent());

    return d_rowIndex == ROW_INDEX_SENTINEL;
  }
}; /* class MatrixEntry<T> */

template<class T>
class MatrixEntryVector {
private:
  typedef MatrixEntry<T> EntryType;
  typedef std::vector<EntryType> EntryArray;

  EntryArray d_entries;
  std::queue<EntryID> d_freedEntries;

  uint32_t d_size;

public:
  MatrixEntryVector():
    d_entries(), d_freedEntries(), d_size(0)
  {}

  const EntryType& operator[](EntryID id) const{
    Assert(inBounds(id));
    return d_entries[id];
  }

  EntryType& get(EntryID id){
    Assert(inBounds(id));
    return d_entries[id];
  }

  void freeEntry(EntryID id){
    Assert(get(id).blank());
    Assert(d_size > 0);

    d_freedEntries.push(id);
    --d_size;
  }

  EntryID newEntry(){
    EntryID newId;
    if(d_freedEntries.empty()){
      newId = d_entries.size();
      d_entries.push_back(MatrixEntry<T>());
    }else{
      newId = d_freedEntries.front();
      d_freedEntries.pop();
    }
    ++d_size;
    return newId;
  }

  uint32_t size() const{ return d_size; }
  uint32_t capacity() const{ return d_entries.capacity(); }


private:
  bool inBounds(EntryID id) const{
    return id <  d_entries.size();
  }
}; /* class MatrixEntryVector<T> */

template <class T, bool isRow>
class MatrixVector {
private:
  EntryID d_head;
  uint32_t d_size;

  MatrixEntryVector<T>* d_entries;

  class Iterator {
  private:
    EntryID d_curr;
    const MatrixEntryVector<T>* d_entries;

  public:
    Iterator(EntryID start, const MatrixEntryVector<T>* entries) :
      d_curr(start), d_entries(entries)
    {}

  public:

    EntryID getID() const {
      return d_curr;
    }

    const MatrixEntry<T>& operator*() const{
      Assert(!atEnd());
      return (*d_entries)[d_curr];
    }

    Iterator& operator++(){
      Assert(!atEnd());
      const MatrixEntry<T>& entry = (*d_entries)[d_curr];
      d_curr = isRow ? entry.getNextRowEntryID() : entry.getNextColEntryID();
      return *this;
    }

    bool atEnd() const {
      return d_curr == ENTRYID_SENTINEL;
    }

    bool operator==(const Iterator& i) const{
      return d_curr == i.d_curr && d_entries == i.d_entries;
    }

    bool operator!=(const Iterator& i) const{
      return !(d_curr == i.d_curr && d_entries == i.d_entries);
    }
  }; /* class MatrixVector<T, isRow>::Iterator */

public:
  MatrixVector(MatrixEntryVector<T>* mev)
    : d_head(ENTRYID_SENTINEL), d_size(0), d_entries(mev)
  {}

  MatrixVector(EntryID head, uint32_t size, MatrixEntryVector<T>* mev)
    : d_head(head), d_size(size), d_entries(mev)
  {}

  typedef Iterator const_iterator;
  const_iterator begin() const {
    return Iterator(d_head, d_entries);
  }
  const_iterator end() const {
    return Iterator(ENTRYID_SENTINEL, d_entries);
  }

  EntryID getHead() const { return d_head; }

  uint32_t getSize() const { return d_size; }

  void insert(EntryID newId){
    if(isRow){
      d_entries->get(newId).setNextRowEntryID(d_head);

      if(d_head != ENTRYID_SENTINEL){
        d_entries->get(d_head).setPrevRowEntryID(newId);
      }
    }else{
      d_entries->get(newId).setNextColEntryID(d_head);

      if(d_head != ENTRYID_SENTINEL){
        d_entries->get(d_head).setPrevColEntryID(newId);
      }
    }

    d_head = newId;
    ++d_size;
  }
  void remove(EntryID id){
    Assert(d_size > 0);
    --d_size;
    if(isRow){
      EntryID prevRow = d_entries->get(id).getPrevRowEntryID();
      EntryID nextRow = d_entries->get(id).getNextRowEntryID();

      if(d_head == id){
        d_head = nextRow;
      }
      if(prevRow != ENTRYID_SENTINEL){
        d_entries->get(prevRow).setNextRowEntryID(nextRow);
      }
      if(nextRow != ENTRYID_SENTINEL){
        d_entries->get(nextRow).setPrevRowEntryID(prevRow);
      }
    }else{
      EntryID prevCol = d_entries->get(id).getPrevColEntryID();
      EntryID nextCol = d_entries->get(id).getNextColEntryID();

      if(d_head == id){
        d_head = nextCol;
      }

      if(prevCol != ENTRYID_SENTINEL){
        d_entries->get(prevCol).setNextColEntryID(nextCol);
      }
      if(nextCol != ENTRYID_SENTINEL){
        d_entries->get(nextCol).setPrevColEntryID(prevCol);
      }
    }
  }
}; /* class MatrixVector<T, isRow> */

template <class T>
  class RowVector : public MatrixVector<T, true>
{
private:
  typedef MatrixVector<T, true> SuperT;
public:
  typedef typename SuperT::const_iterator const_iterator;

  RowVector(MatrixEntryVector<T>* mev) : SuperT(mev){}
};/* class RowVector<T> */

template <class T>
  class ColumnVector : public MatrixVector<T, false>
{
private:
  typedef MatrixVector<T, false> SuperT;
public:
  typedef typename SuperT::const_iterator const_iterator;

  ColumnVector(MatrixEntryVector<T>* mev) : SuperT(mev){}
};/* class ColumnVector<T> */

template <class T>
class Matrix {
protected:

  typedef MatrixEntry<T> Entry;

  typedef CVC4::theory::arith::RowVector<T> RowVectorT;
  typedef typename RowVectorT::const_iterator RowIterator;

  typedef CVC4::theory::arith::ColumnVector<T> ColumnVectorT;
  typedef typename ColumnVectorT::const_iterator ColIterator;

  // RowTable : RowID |-> RowVector
  typedef std::vector< RowVectorT > RowTable;
  RowTable d_rows;

  // ColumnTable : ArithVar |-> ColumnVector
  typedef std::vector< ColumnVectorT > ColumnTable;
  ColumnTable d_columns;

  /* The merge buffer is used to store a row in order to optimize row addition. */
  typedef std::pair<EntryID, bool> PosUsedPair;
  typedef DenseMap< PosUsedPair > RowToPosUsedPairMap;
  RowToPosUsedPairMap d_mergeBuffer;

  /* The row that is in the merge buffer. */
  RowIndex d_rowInMergeBuffer;

  uint32_t d_entriesInUse;
  MatrixEntryVector<T> d_entries;

  std::vector<RowIndex> d_pool;

  T d_zero;

public:
  /**
   * Constructs an empty Matrix.
   */
  Matrix()
  : d_rows(),
    d_columns(),
    d_mergeBuffer(),
    d_rowInMergeBuffer(ROW_INDEX_SENTINEL),
    d_entriesInUse(0),
    d_entries(),
    d_zero(0)
  {}

  Matrix(const T& zero)
  : d_rows(),
    d_columns(),
    d_mergeBuffer(),
    d_rowInMergeBuffer(ROW_INDEX_SENTINEL),
    d_entriesInUse(0),
    d_entries(),
    d_zero(zero)
  {}


protected:

  void addEntry(RowIndex row, ArithVar col, const T& coeff){
    Debug("tableau") << "addEntry(" << row << "," << col <<"," << coeff << ")" << std::endl;

    Assert(coeff != 0);
    Assert(row < d_rows.size());
    Assert(col < d_columns.size());

    EntryID newId = d_entries.newEntry();
    Entry& newEntry = d_entries.get(newId);
    newEntry = Entry(row, col, coeff);

    Assert(newEntry.getCoefficient() != 0);


    ++d_entriesInUse;

    d_rows[row].insert(newId);
    d_columns[col].insert(newId);
  }

  void removeEntry(EntryID id){
    Assert(d_entriesInUse > 0);
    --d_entriesInUse;

    Entry& entry = d_entries.get(id);

    RowIndex ridx = entry.getRowIndex();
    ArithVar col = entry.getColVar();

    Assert(d_rows[ridx].getSize() > 0);
    Assert(d_columns[col].getSize() > 0);

    d_rows[ridx].remove(id);
    d_columns[col].remove(id);

    entry.markBlank();

    d_entries.freeEntry(id);
  }

 private:
  RowIndex requestRowIndex(){
    if(d_pool.empty()){
      RowIndex ridx = d_rows.size();
      d_rows.push_back(RowVectorT(&d_entries));
      return ridx;
    }else{
      RowIndex rid = d_pool.back();
      d_pool.pop_back();
      return rid;
    }
  }

  void releaseRowIndex(RowIndex rid){
    d_pool.push_back(rid);
  }

public:

  size_t getNumRows() const {
    return d_rows.size();
  }

  size_t getNumColumns() const {
    return d_columns.size();
  }

  void increaseSize(){
    d_columns.push_back(ColumnVector<T>(&d_entries));
  }

  const RowVector<T>& getRow(RowIndex r) const {
    Assert(r < d_rows.size());
    return d_rows[r];
  }

  const ColumnVector<T>& getColumn(ArithVar v) const {
    Assert(v < d_columns.size());
    return d_columns[v];
  }

  uint32_t getRowLength(RowIndex r) const{
    return getRow(r).getSize();
  }

  uint32_t getColLength(ArithVar x) const{
    return getColumn(x).getSize();
  }

  /**
   * Adds a row to the matrix.
   * The new row is equivalent to:
   *   \f$\sum_i\f$ coeffs[i] * variables[i]
   */
  RowIndex addRow(const std::vector<T>& coeffs,
                  const std::vector<ArithVar>& variables){

    RowIndex ridx = requestRowIndex();

    //RowIndex ridx = d_rows.size();
    //d_rows.push_back(RowVectorT(&d_entries));

    std::vector<Rational>::const_iterator coeffIter = coeffs.begin();
    std::vector<ArithVar>::const_iterator varsIter = variables.begin();
    std::vector<ArithVar>::const_iterator varsEnd = variables.end();

    for(; varsIter != varsEnd; ++coeffIter, ++varsIter){
      const Rational& coeff = *coeffIter;
      ArithVar var_i = *varsIter;
      Assert(var_i < getNumColumns());
      addEntry(ridx, var_i, coeff);
    }

    return ridx;
  }


  void loadRowIntoBuffer(RowIndex rid){
    Assert(d_mergeBuffer.empty());
    Assert(d_rowInMergeBuffer == ROW_INDEX_SENTINEL);

    RowIterator i = getRow(rid).begin(), i_end = getRow(rid).end();
    for(; i != i_end; ++i){
      EntryID id = i.getID();
      const MatrixEntry<T>& entry = *i;
      ArithVar colVar = entry.getColVar();
      d_mergeBuffer.set(colVar, std::make_pair(id, false));
    }

    d_rowInMergeBuffer = rid;
  }

  void clearBuffer() {
    Assert(d_rowInMergeBuffer != ROW_INDEX_SENTINEL);

    d_rowInMergeBuffer = ROW_INDEX_SENTINEL;
    d_mergeBuffer.purge();
  }

  /**  to += mult * buffer. */
  void rowPlusBufferTimesConstant(RowIndex to, const T& mult){
    Assert(d_rowInMergeBuffer != ROW_INDEX_SENTINEL);
    Assert(to != ROW_INDEX_SENTINEL);

    Debug("tableau") << "rowPlusRowTimesConstant("
                     << to << "," << mult << "," << d_rowInMergeBuffer << ")"
                     << std::endl;

    Assert(debugNoZeroCoefficients(to));
    Assert(debugNoZeroCoefficients(d_rowInMergeBuffer));

    Assert(mult != 0);


    RowIterator i = getRow(to).begin();
    RowIterator i_end = getRow(to).end();
    while(i != i_end){
      EntryID id = i.getID();
      Entry& entry = d_entries.get(id);
      ArithVar colVar = entry.getColVar();

      ++i;

      if(d_mergeBuffer.isKey(colVar)){
        EntryID bufferEntry = d_mergeBuffer[colVar].first;
        Assert(!d_mergeBuffer[colVar].second);
        d_mergeBuffer.get(colVar).second = true;

        const Entry& other = d_entries.get(bufferEntry);
        entry.getCoefficient() += mult * other.getCoefficient();

        if(entry.getCoefficient() == d_zero){
          removeEntry(id);
        }
      }
    }

    i = getRow(d_rowInMergeBuffer).begin();
    i_end = getRow(d_rowInMergeBuffer).end();

    for(; i != i_end; ++i){
      const Entry& entry = *i;
      ArithVar colVar = entry.getColVar();

      if(d_mergeBuffer[colVar].second){
        d_mergeBuffer.get(colVar).second = false;
      }else{
        Assert(!(d_mergeBuffer[colVar]).second);
        T newCoeff =  mult * entry.getCoefficient();
        addEntry(to, colVar, newCoeff);
      }
    }

    Assert(mergeBufferIsClear());

    if(Debug.isOn("matrix")) { printMatrix(); }
  }

  bool mergeBufferIsClear() const{
    RowToPosUsedPairMap::const_iterator i = d_mergeBuffer.begin();
    RowToPosUsedPairMap::const_iterator i_end = d_mergeBuffer.end();
    for(; i != i_end; ++i){
      RowIndex rid = *i;
      if(d_mergeBuffer[rid].second){
        return false;
      }
    }
    return true;
  }

protected:

  EntryID findOnRow(RowIndex rid, ArithVar column){
    RowIterator i = d_rows[rid].begin(), i_end = d_rows[rid].end();
    for(; i != i_end; ++i){
      EntryID id = i.getID();
      const MatrixEntry<T>& entry = *i;
      ArithVar colVar = entry.getColVar();

      if(colVar == column){
        return id;
      }
    }
    return ENTRYID_SENTINEL;
  }

  EntryID findOnCol(RowIndex rid, ArithVar column){
    ColIterator i = d_columns[column].begin(), i_end = d_columns[column].end();
    for(; i != i_end; ++i){
      EntryID id = i.getID();
      const MatrixEntry<T>& entry = *i;
      RowIndex currRow = entry.getRowIndex();

      if(currRow == rid){
        return id;
      }
    }
    return ENTRYID_SENTINEL;
  }

  MatrixEntry<T> d_failedFind;
public:

  /** If the find fails, isUnused is true on the entry. */
  const MatrixEntry<T>& findEntry(RowIndex rid, ArithVar col){
    bool colIsShorter = getColLength(col) < getRowLength(rid);
    EntryID id = colIsShorter ? findOnCol(rid, col) : findOnRow(rid,col);
    if(id == ENTRYID_SENTINEL){
      return d_failedFind;
    }else{
      return d_entries.get(id);
    }
  }

  /**
   * Prints the contents of the Matrix to Debug("matrix")
   */
  void printMatrix() const {
    Debug("matrix") << "Matrix::printMatrix"  << std::endl;

    for(RowIndex i = 0, N = d_rows.size(); i < N; ++i){
      printRow(i);
    }
  }

  void printRow(RowIndex rid) const {
    Debug("matrix") << "{" << rid << ":";
    const RowVector<T>& row = getRow(rid);
    RowIterator i = row.begin();
    RowIterator i_end = row.end();
    for(; i != i_end; ++i){
      printEntry(*i);
      Debug("matrix") << ",";
    }
    Debug("matrix") << "}" << std::endl;
  }

  void printEntry(const MatrixEntry<T>& entry) const {
    Debug("matrix") << entry.getColVar() << "*" << entry.getCoefficient();
  }


protected:

  // static bool bufferPairIsNotEmpty(const PosUsedPair& p){
  //   return !(p.first == ENTRYID_SENTINEL && p.second == false);
  // }

  // static bool bufferPairIsEmpty(const PosUsedPair& p){
  //   return (p.first == ENTRYID_SENTINEL && p.second == false);
  // }
  // bool mergeBufferIsEmpty() const {
  //   return d_mergeBuffer.end() == std::find_if(d_mergeBuffer.begin(),
  //                                              d_mergeBuffer.end(),
  //                                              bufferPairIsNotEmpty);
  // }

public:
  uint32_t size() const {
    return d_entriesInUse;
  }
  uint32_t getNumEntriesInTableau() const {
    return d_entries.size();
  }
  uint32_t getEntryCapacity() const {
    return d_entries.capacity();
  }

  void removeRow(RowIndex rid){
    RowIterator i = getRow(rid).begin();
    RowIterator i_end = getRow(rid).end();
    for(; i != i_end; ++i){
      EntryID id = i.getID();
      removeEntry(id);
    }
    releaseRowIndex(rid);
  }

  double densityMeasure() const{
    Assert(numNonZeroEntriesByRow() == numNonZeroEntries());
    Assert(numNonZeroEntriesByCol() == numNonZeroEntries());

    uint32_t n = getNumRows();
    if(n == 0){
      return 1.0;
    }else {
      uint32_t s = numNonZeroEntries();
      uint32_t m = d_columns.size();
      uint32_t divisor = (n *(m - n + 1));

      Assert(n >= 1);
      Assert(m >= n);
      Assert(divisor > 0);
      Assert(divisor >= s);

      return (double(s)) / divisor;
    }
  }

  void loadSignQueries(RowIndex rid, DenseMap<int>& target) const{

    RowIterator i = getRow(rid).begin(), i_end = getRow(rid).end();
    for(; i != i_end; ++i){
      const MatrixEntry<T>& entry = *i;
      target.set(entry.getColVar(), entry.getCoefficient().sgn());
    }
  }

protected:
  uint32_t numNonZeroEntries() const { return size(); }

  uint32_t numNonZeroEntriesByRow() const {
    uint32_t rowSum = 0;
    for(RowIndex rid = 0, N = d_rows.size(); rid < N; ++rid){
      rowSum += getRowLength(rid);
    }
    return rowSum;
  }

  uint32_t numNonZeroEntriesByCol() const {
    uint32_t colSum = 0;
    for(ArithVar v = 0, N = d_columns.size(); v < N; ++v){
      colSum += getColLength(v);
    }
    return colSum;
  }


  bool debugNoZeroCoefficients(RowIndex ridx){
    for(RowIterator i=getRow(ridx).begin(); !i.atEnd(); ++i){
      const Entry& entry = *i;
      if(entry.getCoefficient() == 0){
        return false;
      }
    }
    return true;
  }
  bool debugMatchingCountsForRow(RowIndex ridx){
    for(RowIterator i=getRow(ridx).begin(); !i.atEnd(); ++i){
      const Entry& entry = *i;
      ArithVar colVar = entry.getColVar();
      uint32_t count = debugCountColLength(colVar);
      Debug("tableau") << "debugMatchingCountsForRow "
                       << ridx << ":" << colVar << " " << count
                       <<" "<< getColLength(colVar) << std::endl;
      if( count != getColLength(colVar) ){
        return false;
      }
    }
    return true;
  }

  uint32_t debugCountColLength(ArithVar var){
    Debug("tableau") << var << " ";
    uint32_t count = 0;
    for(ColIterator i=getColumn(var).begin(); !i.atEnd(); ++i){
      const Entry& entry = *i;
      Debug("tableau") << "(" << entry.getRowIndex() << ", " << i.getID() << ") ";
      ++count;
    }
    Debug("tableau") << std::endl;
    return count;
  }
  uint32_t debugCountRowLength(RowIndex ridx){
    uint32_t count = 0;
    for(RowIterator i=getRow(ridx).begin(); !i.atEnd(); ++i){
      ++count;
    }
    return count;
  }

};/* class Matrix<T> */


/**
 * A Tableau is a Rational matrix that keeps its rows in solved form.
 * Each row has a basic variable with coefficient -1 that is solved.
 * Tableau is optimized for pivoting.
 * The tableau should only be updated via pivot calls.
 */
class Tableau : public Matrix<Rational> {
public:
private:
  typedef DenseMap<RowIndex> BasicToRowMap;
  // Set of all of the basic variables in the tableau.
  // ArithVarMap<RowIndex> : ArithVar |-> RowIndex
  BasicToRowMap d_basic2RowIndex;

  // RowIndex |-> Basic Variable
  typedef DenseMap<ArithVar> RowIndexToBasicMap;
  RowIndexToBasicMap d_rowIndex2basic;

public:

  Tableau() : Matrix<Rational>(Rational(0)) {}

  typedef Matrix<Rational>::ColIterator ColIterator;
  typedef Matrix<Rational>::RowIterator RowIterator;
  typedef BasicToRowMap::const_iterator BasicIterator;

  typedef MatrixEntry<Rational> Entry;

  bool isBasic(ArithVar v) const{
    return d_basic2RowIndex.isKey(v);
  }

  void debugPrintIsBasic(ArithVar v) const {
    if(isBasic(v)){
      Warning() << v << " is basic." << std::endl;
    }else{
      Warning() << v << " is non-basic." << std::endl;
    }
  }

  BasicIterator beginBasic() const {
    return d_basic2RowIndex.begin();
  }
  BasicIterator endBasic() const {
    return d_basic2RowIndex.end();
  }

  RowIndex basicToRowIndex(ArithVar x) const {
    return d_basic2RowIndex[x];
  }

  ArithVar rowIndexToBasic(RowIndex rid) const {
    Assert(rid < d_rowIndex2basic.size());
    return d_rowIndex2basic[rid];
  }

  ColIterator colIterator(ArithVar x) const {
    return getColumn(x).begin();
  }

  RowIterator basicRowIterator(ArithVar basic) const {
    return getRow(basicToRowIndex(basic)).begin();
  }

  /**
   * Adds a row to the tableau.
   * The new row is equivalent to:
   *   basicVar = \f$\sum_i\f$ coeffs[i] * variables[i]
   * preconditions:
   *   basicVar is already declared to be basic
   *   basicVar does not have a row associated with it in the tableau.
   *
   * Note: each variables[i] does not have to be non-basic.
   * Pivoting will be mimicked if it is basic.
   */
  void addRow(ArithVar basicVar,
              const std::vector<Rational>& coeffs,
              const std::vector<ArithVar>& variables);

  /**
   * preconditions:
   *   x_r is basic,
   *   x_s is non-basic, and
   *   a_rs != 0.
   */
  void pivot(ArithVar basicOld, ArithVar basicNew);

  void removeBasicRow(ArithVar basic);

private:
  /* Changes the basic variable on the row for basicOld to basicNew. */
  void rowPivot(ArithVar basicOld, ArithVar basicNew);

};/* class Tableau */

}/* CVC4::theory::arith namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

