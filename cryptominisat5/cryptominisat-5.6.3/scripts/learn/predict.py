#!/usr/bin/env python3
# -*- coding: utf-8 -*-

# Copyright (C) 2018  Mate Soos
#
# This program is free software; you can redistribute it and/or
# modify it under the terms of the GNU General Public License
# as published by the Free Software Foundation; version 2
# of the License.
#
# This program is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# GNU General Public License for more details.
#
# You should have received a copy of the GNU General Public License
# along with this program; if not, write to the Free Software
# Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA
# 02110-1301, USA.

import pandas as pd
import pickle
import sklearn
import sklearn.svm
import sklearn.tree
import sklearn.ensemble
import optparse
import numpy as np
import sklearn.metrics
import time
import itertools
import matplotlib.pyplot as plt
from sklearn.model_selection import train_test_split

class_names = ["throw", "longer"]
cuts = [-1, 10000, 1000000000000]
class_names2 = ["middle", "forever"]
cuts2 = [-1, 30000, 1000000000000]
#class_names3 = ["middle2", "forever"]
#cuts3 = [-1, 60000, 1000000000000]


def output_to_dot(clf, features, nameextra):
    fname = options.dot+nameextra
    sklearn.tree.export_graphviz(clf, out_file=fname,
                                 feature_names=features,
                                 class_names=class_names,
                                 filled=True, rounded=True,
                                 special_characters=True,
                                 proportion=True)
    print("Run dot:")
    print("dot -Tpng {fname} -o {fname}.png".format(fname=fname))
    print("gwenview {fname}.png".format(fname=fname))


def calc_cross_val():
    # calculate accuracy/prec/recall for cross-validation
    accuracy = sklearn.model_selection.cross_val_score(self.clf, X_train, y_train, cv=10)
    precision = sklearn.model_selection.cross_val_score(self.clf, X_train, y_train, cv=10, scoring='precision')
    recall = sklearn.model_selection.cross_val_score(self.clf, X_train, y_train, cv=10, scoring='recall')
    print("cv-accuracy:", accuracy)
    print("cv-precision:", precision)
    print("cv-recall:", recall)
    accuracy = np.mean(accuracy)
    precision = np.mean(precision)
    recall = np.mean(recall)
    print("cv-prec: %-3.4f  cv-recall: %-3.4f cv-accuracy: %-3.4f T: %-3.2f" %
          (precision, recall, accuracy, (time.time() - t)))


def plot_confusion_matrix(cm, classes,
                          normalize=False,
                          title='Confusion matrix',
                          cmap=plt.cm.Blues):
    """
    This function prints and plots the confusion matrix.
    Normalization can be applied by setting `normalize=True`.
    """
    if normalize:
        cm = cm.astype('float') / cm.sum(axis=1)[:, np.newaxis]
        print("Normalized confusion matrix")
    else:
        print('Confusion matrix, without normalization')

    print(cm)

    plt.imshow(cm, interpolation='nearest', cmap=cmap)
    plt.title(title)
    plt.colorbar()
    tick_marks = np.arange(len(classes))
    plt.xticks(tick_marks, classes, rotation=45)
    plt.yticks(tick_marks, classes)

    fmt = '.2f' if normalize else 'd'
    thresh = cm.max() / 2.
    for i, j in itertools.product(range(cm.shape[0]), range(cm.shape[1])):
        plt.text(j, i, format(cm[i, j], fmt),
                 horizontalalignment="center",
                 color="white" if cm[i, j] > thresh else "black")

    plt.tight_layout()
    plt.ylabel('True label')
    plt.xlabel('Predicted label')


# to check for too large or NaN values:
def check_too_large_or_nan_values(df):
    features = df.columns.values.flatten().tolist()
    index = 0
    for index, row in df.iterrows():
        for x, name in zip(row, features):
            if not np.isfinite(x) or x > np.finfo(np.float32).max:
                print("issue with data for features: ", name, x)
            index += 1


def get_code(tree, feature_names):
    left = tree.tree_.children_left
    right = tree.tree_.children_right
    threshold = tree.tree_.threshold
    features = [feature_names[i] for i in tree.tree_.feature]
    value = tree.tree_.value

    def recurse(left, right, threshold, features, node):
        if (threshold[node] != -2):
            print("if ( " + features[node] + " <= " + str(threshold[node]) + " ) {")
            if left[node] != -1:
                recurse(left, right, threshold, features, left[node])
            print("} else {")
            if right[node] != -1:
                recurse(left, right, threshold, features, right[node])
            print("}")
        else:
            print("return " + str(value[node]))

    recurse(left, right, threshold, features, 0)


def one_classifier(df, features, to_predict, names, w_name, w_number, final):
    print("================ predicting %s ================" % to_predict)
    print("-> Number of features  :", len(features))
    print("-> Number of datapoints:", df.shape)
    print("-> Predicting          :", to_predict)

    train, test = train_test_split(df, test_size=0.33)
    X_train = train[features]
    y_train = train[to_predict]
    X_test = test[features]
    y_test = test[to_predict]

    t = time.time()
    clf = None
    # clf = sklearn.linear_model.LogisticRegression()
    # clf = sklearn.svm.SVC()
    if final:
        clf = sklearn.tree.DecisionTreeClassifier(max_depth=options.tree_depth)
    else:
        clf = sklearn.ensemble.RandomForestClassifier(n_estimators=80)
        #clf = sklearn.ensemble.ExtraTreesClassifier(n_estimators=80)

    sample_weight = [w_number if i == w_name else 1 for i in y_train]
    clf.fit(X_train, y_train, sample_weight=sample_weight)

    print("Training finished. T: %-3.2f" % (time.time() - t))

    best_features = []
    if not final:
        importances = clf.feature_importances_
        std = np.std([tree.feature_importances_ for tree in clf.estimators_], axis=0)
        indices = np.argsort(importances)[::-1]
        indices = indices[:options.top_num_features]
        myrange = min(X_train.shape[1], options.top_num_features)

        # Print the feature ranking
        print("Feature ranking:")

        for f in range(myrange):
            print("%-3d  %-35s -- %8.4f" %
                  (f + 1, features[indices[f]], importances[indices[f]]))
            best_features.append(features[indices[f]])

        # Plot the feature importances of the clf
        plt.figure()
        plt.title("Feature importances")
        plt.bar(range(myrange), importances[indices],
                color="r", align="center"
                , yerr=std[indices])
        plt.xticks(range(myrange), [features[x] for x in indices], rotation=45)
        plt.xlim([-1, myrange])
    else:
        get_code(clf, features)

    print("Calculating scores....")
    y_pred = clf.predict(X_test)
    accuracy = sklearn.metrics.accuracy_score(y_test, y_pred)
    precision = sklearn.metrics.precision_score(y_test, y_pred, average="macro")
    recall = sklearn.metrics.recall_score(y_test, y_pred, average="macro")
    print("prec: %-3.4f  recall: %-3.4f accuracy: %-3.4f T: %-3.2f" % (
        precision, recall, accuracy, (time.time() - t)))

    if options.confusion:
        sample_weight = [w_number if i == w_name else 1 for i in y_pred]
        cnf_matrix = sklearn.metrics.confusion_matrix(
            y_test, y_pred, labels=names, sample_weight=sample_weight)

        np.set_printoptions(precision=2)

        # Plot non-normalized confusion matrix
        plt.figure()
        plot_confusion_matrix(
            cnf_matrix, classes=names,
            title='Confusion matrix, without normalization')

        # Plot normalized confusion matrix
        plt.figure()
        plot_confusion_matrix(
            cnf_matrix, classes=names, normalize=True,
            title='Normalized confusion matrix')

    # TODO do L1 regularization

    if False:
        calc_cross_val()

    if options.dot is not None and final:
        output_to_dot(clf, features, names[0])

    return best_features


def remove_old_clause_features(features):
    todel = []
    for name in features:
        if "cl2" in name or "cl3" in name or "cl4" in name:
            todel.append(name)

    for x in todel:
        features.remove(x)
        if options.verbose:
            print("Removing old clause feature:", x)


def rem_features(feat, to_remove):
    feat_less = list(feat)
    todel = []
    for feature in feat:
        for rem in to_remove:
            if rem in feature:
                feat_less.remove(feature)
                if options.verbose:
                    print("Removing feature from feat_less:", feature)

    return feat_less


def learn(fname):
    with open(fname, "rb") as f:
        df = pickle.load(f)

    if options.check_row_data:
        check_too_large_or_nan_values(df)

    print("total samples: %5d" % df.shape[0])

    # lifetime to predict
    df["x.lifetime_cut"] = pd.cut(
        df["x.lifetime"],
        cuts,
        labels=class_names)

    df["x.lifetime_cut2"] = pd.cut(
        df["x.lifetime"],
        cuts2,
        labels=class_names2)

    #df["x.lifetime_cut3"] = pd.cut(
        #df["x.lifetime"],
        #cuts3,
        #labels=class_names3)

    features = df.columns.values.flatten().tolist()
    features = rem_features(features,
                            ["x.num_used", "x.class", "x.lifetime", "fname"])

    # this needs binarization
    features = rem_features(features, ["cl.cur_restart_type"])
    # x = (df["cl.cur_restart_type"].values[:, np.newaxis] == df["cl.cur_restart_type"].unique()).astype(int)
    # print(x)

    if True:
        remove_old_clause_features(features)

    if options.raw_data_plots:
        pd.options.display.mpl_style = "default"
        df.hist()
        df.boxplot()

    if True:
        feat_less = rem_features(features, ["rdb1", "rdb2", "rdb3", "rdb4"])
        best_feats = one_classifier(df, feat_less, "x.lifetime_cut",
                                    class_names, "longer", 17,
                                    False)
        if options.show:
            plt.show()

        one_classifier(df, best_feats, "x.lifetime_cut",
                       class_names, "longer", 3,
                       True)
        if options.show:
            plt.show()

    if True:
        feat_less = rem_features(features, ["rdb3", "rdb4"])
        df2 = df[df["x.lifetime"] > cuts[1]]

        best_feats = one_classifier(df2, feat_less, "x.lifetime_cut2",
                                    class_names2, "middle", 30,
                                    False)
        if options.show:
            plt.show()

        one_classifier(df2, best_feats, "x.lifetime_cut2",
                       class_names2, "middle", 4,
                       True)

        if options.show:
            plt.show()

    #if True:
        #df3 = df[df["x.lifetime"] > cuts2[1]]

        #best_feats = one_classifier(df3, features, "x.lifetime_cut3",
                                    #class_names3, "middle2", 20,
                                    #False)
        #if options.show:
            #plt.show()

        #one_classifier(df3, best_feats, "x.lifetime_cut3",
                       #class_names3, "middle2", 8,
                       #True)


if __name__ == "__main__":
    usage = "usage: %prog [options] file.pandas"
    parser = optparse.OptionParser(usage=usage)

    parser.add_option("--verbose", "-v", action="store_true", default=False,
                      dest="verbose", help="Print more output")
    parser.add_option("--cross", action="store_true", default=False,
                      dest="cross_validate", help="Cross-validate prec/recall/acc against training data")
    parser.add_option("--depth", default=6, type=int,
                      dest="tree_depth", help="Depth of the tree to create")
    parser.add_option("--dot", type=str, default=None,
                      dest="dot", help="Create DOT file")
    parser.add_option("--conf", action="store_true", default=False,
                      dest="confusion", help="Create confusion matrix")
    parser.add_option("--show", action="store_true", default=False,
                      dest="show", help="Show visual graphs")
    parser.add_option("--check", action="store_true", default=False,
                      dest="check_row_data", help="Check row data for NaN or float overflow")
    parser.add_option("--rawplots", action="store_true", default=False,
                      dest="raw_data_plots", help="Display raw data plots")
    parser.add_option("--top", default=12, type=int,
                      dest="top_num_features", help="Number of top features to take to generate the final predictor")

    (options, args) = parser.parse_args()

    if len(args) < 1:
        print("ERROR: You must give the pandas file!")
        exit(-1)

    learn(args[0])
