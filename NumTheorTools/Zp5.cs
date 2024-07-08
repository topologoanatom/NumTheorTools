using System;
using System.Collections.Generic;
using System.Linq;
using System.Numerics;
using System.Text;
using System.Threading.Tasks;

namespace NumTheorTools
{
    internal struct Zp5BIG
    {
        public BigInteger RealPart;
        public BigInteger QuadraticPart;
        public BigInteger p;
        public BigInteger Norm { get { return getNorm(this); } }
        public BigInteger Ord { get { return getOrd(this); } }


        public Zp5BIG(BigInteger realPart, BigInteger quadraticPart, BigInteger m)
        {
            this.RealPart = NumTools.Mod(realPart, m);
            this.QuadraticPart = NumTools.Mod(quadraticPart, m);
            this.p = m;
        }
        public static Zp5BIG operator +(Zp5BIG a, Zp5BIG b) => new Zp5BIG(a.RealPart + b.RealPart, a.QuadraticPart + b.QuadraticPart, a.p);
        public static Zp5BIG operator +(Zp5BIG a, BigInteger b) => new Zp5BIG(a.RealPart + b, a.QuadraticPart, a.p);
        public static Zp5BIG operator +(BigInteger b, Zp5BIG a) => new Zp5BIG(a.RealPart + b, a.QuadraticPart, a.p);
        public static Zp5BIG operator -(Zp5BIG a, Zp5BIG b) => new Zp5BIG(a.RealPart - b.RealPart, a.QuadraticPart - b.QuadraticPart, a.p);
        public static Zp5BIG operator -(Zp5BIG a) => new Zp5BIG(-a.RealPart, -a.QuadraticPart, a.p);
        public static Zp5BIG operator -(Zp5BIG a, BigInteger b) => new Zp5BIG(a.RealPart - b, a.QuadraticPart, a.p);
        public static Zp5BIG operator -(BigInteger b, Zp5BIG a) => new Zp5BIG(a.RealPart - b, a.QuadraticPart, a.p);
        public static Zp5BIG operator *(Zp5BIG a, Zp5BIG b) => new Zp5BIG(a.RealPart * b.RealPart + 5 * a.QuadraticPart * b.QuadraticPart, a.RealPart * b.QuadraticPart + a.QuadraticPart * b.RealPart, a.p);
        public static Zp5BIG operator *(Zp5BIG a, BigInteger b) => new Zp5BIG(a.RealPart * b, a.QuadraticPart * b, a.p);
        public static Zp5BIG operator *(BigInteger b, Zp5BIG a) => new Zp5BIG(a.RealPart * b, a.QuadraticPart * b, a.p);
        public static Zp5BIG operator !(Zp5BIG a) => new Zp5BIG(a.RealPart, -a.QuadraticPart, a.p); // conjugate
        public static Zp5BIG operator /(Zp5BIG a, Zp5BIG b) => new Zp5BIG(getNorm(b), 0, a.p) * a * !b;
        public static Zp5BIG operator ^(Zp5BIG a, BigInteger power) => BinaryRaise(a, power);
        public static bool operator ==(Zp5BIG a, Zp5BIG b) => a.RealPart == b.RealPart && a.QuadraticPart == b.QuadraticPart;
        public static bool operator !=(Zp5BIG a, Zp5BIG b) => a.RealPart != b.RealPart || a.QuadraticPart != b.QuadraticPart;

        public static Zp5BIG BarretReductionRaise(Zp5BIG a, BigInteger power)
        {
            int k = 2 * (int)(a.p.GetBitLength() + 1);
            BigInteger r = (new BigInteger(1) << k) / a.p;
            Zp5BIG result = new Zp5BIG(1, 0, a.p);
            while (power > 0)
            {
                if ((power & 1) == 1)
                {
                    BigInteger realPart = a.RealPart * result.RealPart + 5 * a.QuadraticPart * result.QuadraticPart;
                    BigInteger quadPart = a.RealPart * result.QuadraticPart + a.QuadraticPart * result.RealPart;
                    realPart = realPart - ((realPart * r) >> (k)) * a.p;
                    quadPart = quadPart - ((quadPart * r) >> (k)) * a.p;
                    realPart = realPart < a.p ? realPart : realPart - a.p;
                    quadPart = quadPart < a.p ? quadPart : quadPart - a.p;
                    result.RealPart = realPart;
                    result.QuadraticPart = quadPart;
                }
                power >>= 1;
                BigInteger realPartA = a.RealPart * a.RealPart + 5 * a.QuadraticPart * a.QuadraticPart;
                BigInteger quadPartA = 2 * a.RealPart * a.QuadraticPart;
                realPartA = realPartA - ((realPartA * r) >> (k)) * a.p;
                quadPartA = quadPartA - ((quadPartA * r) >> (k)) * a.p;
                realPartA = realPartA < a.p ? realPartA : realPartA - a.p;
                quadPartA = quadPartA < a.p ? quadPartA : quadPartA - a.p;
                a.RealPart = realPartA;
                a.QuadraticPart = quadPartA;
            }
            return result;
        }
        static BigInteger getOrd(Zp5BIG a)
        {
            Zp5BIG next = a;
            int ord = 1;
            while (next.RealPart != 1 && next.QuadraticPart != 0)
            {
                ord++;
                next *= a;
            }
            return ord;
        }
        public static BigInteger getNorm(Zp5BIG a)
        {
            return NumTools.Mod(a.RealPart * a.RealPart - 5 * a.QuadraticPart * a.QuadraticPart, a.p);
        }
        static Zp5BIG BinaryRaise(Zp5BIG a, BigInteger power)
        {
            Zp5BIG result = new Zp5BIG(1, 0, a.p);
            while (power > 0)
            {
                if ((power & 1) == 1)
                {
                    result = a * result;
                }
                power >>= 1;
                a = new Zp5BIG(a.RealPart * a.RealPart + 5 * a.QuadraticPart * a.QuadraticPart, 2 * a.RealPart * a.QuadraticPart, a.p);
            }
            return result;
        }
        public override string ToString()
        {
            return $"{(this.RealPart, this.QuadraticPart)}";
        }
        public override int GetHashCode()
        {
            return System.HashCode.Combine(this.RealPart, this.QuadraticPart);
        }
        public override bool Equals(object? obj)
        {
            return obj is Zp5BIG other && other.RealPart == this.RealPart && other.QuadraticPart == this.QuadraticPart;
        }
    }
}
