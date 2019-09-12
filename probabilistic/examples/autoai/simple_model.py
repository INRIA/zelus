import argparse
from sklearn import datasets
from sklearn.model_selection import train_test_split
from sklearn.metrics import accuracy_score
from sklearn.svm import SVC
# import matplotlib.pyplot as plt

iris = datasets.load_iris()
digits = datasets.load_digits()

X_train, X_test, y_train, y_test = train_test_split(digits.data, digits.target, test_size=0.2, random_state=42)

parser = argparse.ArgumentParser()
parser.add_argument('--gamma', type=float, default=0.001)
parser.add_argument('--C', type=float, default=100.)
args=parser.parse_args()

clf=SVC(gamma=args.gamma, C=args.C)
clf.fit(X_train, y_train)

predictions=clf.predict(X_test)
accuracy=accuracy_score(y_test, predictions)
print(accuracy)


# Grid search over gamma for future reference 

# accuracies = []
# for gamma in [10**(-n) for n in range(10)]:
#     clf = SVC(gamma=gamma, C=100.)
#     clf.fit(X_train, y_train)
#     predictions=clf.predict(X_test)
#     accuracy = accuracy_score(y_test, predictions)
#     accuracies.append(accuracy)
#     print(f'gamma={gamma}, accuracy={accuracy}')
     
# plt.plot(accuracies)
# plt.show()
 
