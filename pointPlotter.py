from __future__ import print_function

from mpl_toolkits.mplot3d import Axes3D
import matplotlib.pyplot as plt
import numpy as np

fig = plt.figure()
ax = fig.add_subplot(111, projection='3d')

pos = [[1, 1, 0], [1, 0, 0], [1, 2, 0], [1, 3, 0]]
neg = [[1, 4, 0], [1, 5, 0]]
fac = [[0, 1, 0], [0, 1, 3], [0, 2, 0], [0, 2, 3], [0, 4, 0], [0, 5, 0],
        [0, 0, 1], [0, 3, 1], [0, 0, 2], [0, 3, 2], [0, 0, 4], [0, 0, 5], [2, 1, 0], [2, 2, 0], [2, 0, 0]]

xs = []
ys = []
zs = []

for x, y, z in pos + neg + fac:
    print(x, y, z)
    xs.append(x)
    ys.append(y)
    zs.append(z)

print(xs, ys, zs)
ax.scatter(xs, ys, zs)

ax.set_xlim([0, 3])
ax.set_ylim([0, 5])
ax.set_zlim([0, 5])

ax.set_xlabel('X Label')
ax.set_ylabel('Y Label')
ax.set_zlabel('Z Label')

plt.show()
