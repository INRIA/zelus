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

def fit_predict(gamma, C):
    clf=SVC(gamma=gamma, C=C)
    clf.fit(X_train, y_train)
    predictions=clf.predict(X_test)
    return accuracy_score(y_test, predictions)

print(fit_predict(args.gamma, args.C))

# Grid search over gamma for future reference 
# accuracies = []
# gamma = 0.00001
# C = 100.
# # for gamma in [10**(-n) for n in range(10)]:
# for C in range(1,100):
#     accuracy = fit_predict(gamma, C)
#     accuracies.append(accuracy)
#     print(f'gamma={gamma}, C={C}, accuracy={accuracy}')

# import matplotlib.pyplot as plt   
# plt.plot(accuracies)
# plt.show()
 
