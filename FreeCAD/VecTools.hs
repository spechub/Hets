{- |
Module      :  ./FreeCAD/VecTools.hs
Description :  definition of 3-dimensional vector operations, transformations
               between rotation matrices and rotation quaternions
Copyright   :  (c) Robert Savu and Uni Bremen 2011
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Robert.Savu@dfki.de
Stability   :  experimental
Portability :  portable

Declaration of the abstract datatypes of FreeCAD terms
-}

module FreeCAD.VecTools where

import FreeCAD.As

distance3 :: Vector3 -> Vector3 -> Double
distance3 (Vector3 ax ay az) (Vector3 bx by bz) = sqrt (x1 * x1 + x2 * x2 + x3 * x3)
    where
        x1 = ax - bx
        x2 = ay - by
        x3 = az - bz

subtract3 :: Vector3 -> Vector3 -> Vector3
subtract3 a b = Vector3 ex ey ez
    where
        ex = x a - x b
        ey = y a - y b
        ez = z a - z b

norm3 :: Vector3 -> Double
norm3 a = distance3 a (Vector3 0 0 0)

scalarprod3 :: Double -> Vector3 -> Vector3
scalarprod3 a (Vector3 bx by bz) = Vector3 abx aby abz
    where
        abx = a * bx
        aby = a * by
        abz = a * bz

median3 :: [Vector3] -> Vector3
median3 a = scalarprod3 (fromIntegral (length a)) (v3Sum a)

v3Sum :: [Vector3] -> Vector3
v3Sum [] = Vector3 0 0 0
v3Sum [a] = Vector3 (x a) (y a) (z a)
v3Sum [a, b] = Vector3 xc yc zc
    where
        xc = x a * x b
        yc = y a * y b
        zc = z a * z b
v3Sum (a : b : as) = v3Sum (c : as)
    where
        xc = x a * x b
        yc = y a * y b
        zc = z a * z b
        c = Vector3 xc yc zc

v3DotProd :: Vector3 -> Vector3 -> Double
v3DotProd v1 v2 = x v1 * x v2 + y v1 * y v2 + z v1 * z v2

v4DotProd :: Vector4 -> Vector4 -> Double
v4DotProd v1 v2 = q0 v1 * q0 v2 + q1 v1 * q1 v2 + q2 v1 * q2 v2 + q3 v1 * q3 v2

v3VecProd :: Vector3 -> Vector3 -> Vector3
v3VecProd v1 v2 = Vector3 m1 m2 m3
    where
        m1 = y v1 * z v2 - z v1 * y v2
        m2 = z v1 * x v2 - x v1 * z v2
        m3 = x v1 * y v2 - y v1 * x v2

quatProd :: Vector4 -> Vector4 -> Vector4
quatProd v1 v2 = Vector4 m1 m2 m3 m4
    where
        m1 = q3 v2 * q0 v1 + q2 v2 * q1 v1 - q1 v2 * q2 v1 + q0 v2 * q3 v1
        m2 = -q2 v2 * q0 v1 + q3 v2 * q1 v1 + q0 v2 * q2 v1 + q1 v2 * q3 v1
        m3 = q1 v2 * q0 v1 - q0 v2 * q1 v1 + q3 v2 * q2 v1 + q2 v2 * q3 v1
        m4 = -q0 v2 * q0 v1 - q1 v2 * q1 v1 - q2 v2 * q2 v1 + q3 v2 * q3 v1

-- transforms quaternion to rotation matrix
quat2matrix :: Vector4 -> Matrix33
quat2matrix q = Matrix33 m11 m12 m13 m21 m22 m23 m31 m32 m33
             where
                m11 = 1 - 2 * p2 ** 2 - 2 * p3 ** 2
                m12 = 2 * (p1 * p2 - p3 * p4)
                m13 = 2 * (p1 * p3 + p2 * p4)
                m21 = 2 * (p1 * p2 + p3 * p4)
                m22 = 1 - 2 * p1 ** 2 - 2 * p3 ** 2
                m23 = 2 * (p2 * p3 - p1 * p4)
                m31 = 2 * (p1 * p3 - p2 * p4)
                m32 = 2 * (p1 * p4 + p2 * p3)
                m33 = 1 - 2 * p1 ** 2 - 2 * p2 ** 2
                p1 = q0 q
                p2 = q1 q
                p3 = q2 q
                p4 = q3 q

rotate :: Matrix33 -> Vector3 -> Vector3
rotate a v = Vector3 xx yy zz
    where
        xx = a11 a * x v + a12 a * y v + a13 a * z v
        yy = a21 a * x v + a22 a * y v + a23 a * z v
        zz = a31 a * x v + a32 a * y v + a33 a * z v
