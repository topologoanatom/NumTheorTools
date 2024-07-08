
using System.Diagnostics;
using System.Numerics;
using System.Security.Cryptography;
using Dirichlet.Numerics;

class Program 
{
    static void Main() 
    {
        Console.WriteLine(32768 * 32768);
        var x = NumTools.SegmentedSieve(1000000000, 32768);
    }
}
static class QuadraticSieve128
{

    /*
     * Optimal sieve parameters for number's bit lengths ranges - <Number size, number of primes in base, log2 treshold, sieve size>.
     */

    public static List<(int, int, int, int)> sieveConfiguration = new List<(int, int, int, int)>() { ( 64, 255, 30, 1 << 16) , ( 72, 255, 35, 1 << 16), (80, 511, 45, 1 << 18), (88, 3 * 256 - 1, 55, 1 << 19) ,
                                                                                              ( 94, 1023, 60, 1 << 20), ( 104, 6 * 256 - 1, 65, 1 << 20), ( 110, 8 * 256 - 1, 75, 1 << 21) , 
                                                                                              (118, 10 * 256 - 1, 80, 1 << 22) };
    static int SIMDVectorSize = Vector<long>.Count;
    static int SIMDVectorSizeInt16 = Vector<ushort>.Count;
    public static List<Int128> findFactor(Int128 n, List<int> primes, int baseSize, int logTolerance, int intervalSize)
    {
        var watch = new Stopwatch();
        List<int> factorBase = getFactorBase(n, baseSize, primes);
        List<byte> factorBaseLogs = new List<byte>() { };
        List<int> factorBaseRoots = new List<int>();

        foreach (int prime in factorBase)
        {
            factorBaseLogs.Add((byte)Math.Round(Math.Log2(prime)));
            var roots = NumTools.ShanksTonelliInt128(n, prime);
            factorBaseRoots.Add((int)roots.Item2);
        }
        byte[] interval = new byte[intervalSize];
        int[] shifts = new int[baseSize << 1];

        List<ushort[]> smoothValues = new List<ushort[]>();
        List<Int128> smoothArguments = new List<Int128>();
        smoothValues.Capacity = factorBase.Count + 1;
        smoothArguments.Capacity = factorBase.Count + 1;
        // Sieving stage
        Int128 start = Int128.FloorSqrt(n);
        while (smoothArguments.Count < baseSize + 1)
        {
            var s = findBSmooth(n, interval, start, intervalSize, factorBase, factorBaseLogs, factorBaseRoots, logTolerance, shifts);
            smoothArguments.AddRange(s.Item2);
            smoothValues.AddRange(s.Item1);
            start += intervalSize - 1;
        }
        // Exponent vectors of numbers interpreted as array of long values.
        List<long[]> dualMatrix = new List<long[]>();
        for (int i = 0; i < baseSize; i++) 
        {
            long[] dualRow = new long[(baseSize + 1) >> 6];
            long x = 0;
            long counter = 1;
            for (int j = 0; j < baseSize + 1; j++) 
            {
                int value = smoothValues[j][i] & 1;
                x += value * counter;
                counter <<= 1;
                if (counter == 0) 
                {
                    dualRow[j >> 6] = x;
                    x = 0;
                    counter = 1;
                }
            }
            dualMatrix.Add(dualRow);
        }
        var dependentRows = GaussElliminationLong(dualMatrix);

        HashSet<Int128> divisors = new HashSet<Int128>();
        foreach (List<int> dependentSequence in dependentRows)
        {
            List<ushort[]> exponentVectors = new List<ushort[]>();
            Int128 x = 1;
            foreach (int vectorIndex in dependentSequence)
            {
                exponentVectors.Add(smoothValues[vectorIndex]);
                x = Int128.ModMul(x, smoothArguments[vectorIndex], n);
            }
            Int128 y = constructPerfectSquare(exponentVectors, factorBase, n);
            Int128 gcd = Int128.GreatestCommonDivisor(x - y, n);
            if (gcd != n && gcd != 1)
            {
                divisors.Add(gcd);
            }
        }

        List<Int128> coprimeDivisors = new List<Int128>();
        while (divisors.Count != 0)
        {
            Int128 min = divisors.Min();
            divisors.Remove(min);
            foreach (Int128 value in divisors) 
            {
                if (Int128.GreatestCommonDivisor(min, value) != 1) 
                {
                    divisors.Remove(value);
                }
            }
            coprimeDivisors.Add(min);
        }
        return coprimeDivisors;
    }
    static Int128 constructPerfectSquare(List<ushort[]> exponentVectors, List<int> factorBase, Int128 n)
    {
        ushort[] resultVector = new ushort[exponentVectors[0].Length];
        Int128 result = 1;
        foreach (ushort[] vector in exponentVectors)
        {
            AddVectorSIMD(resultVector, vector);
        }
        for (int i = 0; i < resultVector.Length; i++)
        {
            resultVector[i] >>= 1;
            Int128 power = Int128.ModPow(factorBase[i], resultVector[i], n);
            result = Int128.ModMul(result, power, n);
        }
        return result;
    }
    static void AddVectorSIMD(ushort[] a, ushort[] b) 
    {
        int simdPart = a.Length - (a.Length % SIMDVectorSizeInt16);
        for (int i = 0; i < simdPart; i += SIMDVectorSizeInt16) 
        {
            Vector<ushort> v1 = new Vector<ushort>(a, i);
            Vector<ushort> v2 = new Vector<ushort>(b, i);
            v1 += v2;
            v1.CopyTo(a, i);
        }
        for (int i = simdPart; i < a.Length; i++) 
        {
            a[i] += b[i];
        }
    }
    static List<List<int>> GaussElliminationLong(List<long[]> dualMatrix)
    {
        bool[] pivot = new bool[dualMatrix[0].Length << 6];
        Dictionary<int, int> pd = new Dictionary<int, int>();
        for (int j = 0; j < dualMatrix.Count; j++)
        {
            bool pivotFound = false;
            int i = 0;
            int longOffset = 0;
            while (i < dualMatrix[0].Length)
            {
                long value = dualMatrix[j][i];
                for (int k = 0; k < 64; k++) 
                {
                    if ((value & 1) == 1) 
                    {
                        longOffset = k;
                        int index = (i << 6) + k;
                        pivot[index] = true;
                        pivotFound = true;
                        pd[j] = index;
                        break;
                    }
                    value >>= 1;
                }
                if (pivotFound) 
                {
                    break;
                }
                i++;
            }
            if (!pivotFound)
            {
                continue;
            }
            for (int k = 0; k < dualMatrix.Count; k++)
            {
                if (j == k)
                {
                    continue;
                }
                if (((dualMatrix[k][i] >> longOffset) & 1) == 1)
                {
                    AddRowSIMD(j, k, dualMatrix);
                }
            }
        }
        List<List<int>> dependentRows = new List<List<int>>();
        bool[][] transposed = TransposeFromLong(dualMatrix);
        for (int i = 0; i < transposed.Length; i++)
        {
            if (!pivot[i])
            {
                bool[] dRow = transposed[i];
                List<int> dIndexes = new List<int>() { i };
                for (int j = 0; j < dRow.Length; j++)
                {
                    if (dRow[j])
                    {
                        dIndexes.Add(pd[j]);
                    }
                }
                if (dIndexes.Count > 1)
                {
                    dependentRows.Add(dIndexes);
                }
            }
        }
        return dependentRows;
    }
    static bool[][] TransposeFromLong(List<long[]> matrix) 
    {
        bool[][] result = new bool[matrix[0].Length << 6][];
        for (int i = 0; i < matrix[0].Length << 6; i++) 
        {
            result[i] = new bool[matrix.Count];
        }
        for (int i = 0; i < matrix[0].Length; i++) 
        {
            for (int j = 0; j < matrix.Count; j++) 
            {
                long value = matrix[j][i];
                for (int k = 0; k < 64; k++) 
                {
                    result[(i << 6) + k][j] = (value & 1) == 1;
                    value >>= 1;
                }
            }
        }
        return result;
    }
    static void AddRowSIMD(int i, int j, List<long[]> matrix) 
    {
        var row1 = matrix[i];
        var row2 = matrix[j];
        for (int k = 0; k < row1.Length; k += SIMDVectorSize)
        {
            Vector<long> v1 = new Vector<long>(row1, k);
            Vector<long> v2 = new Vector<long>(row2, k);
            v2 ^= v1;
            v2.CopyTo(row2, k);
        }
    }
    static (List<ushort[]>, List<Int128>) findBSmooth(Int128 n, byte[] interval, Int128 start, int intervalSize, List<int> factorBase, List<byte> factorBaseLogs, List<int> factorBaseRoots, int smoothTreshold, int[] shifts)
    {
        List<ushort[]> resultVectors = new List<ushort[]>();
        List<Int128> resultArguments = new List<Int128>();
        var mut = new Mutex();
        Array.Clear(interval);
        Array.Clear(shifts);
        sieve(interval, start, intervalSize, factorBase, factorBaseLogs, factorBaseRoots, shifts);
        Parallel.For(0, intervalSize, () => new ushort[factorBase.Count], (i, _, exponentVector) => 
        {
            if (interval[i] > smoothTreshold)
            {
                Int128 x = start + i;
                bool s = isBSmooth(x * x - n, factorBase, i, shifts, exponentVector);
                if (s)
                {
                    mut.WaitOne();
                    ushort[] copy = new ushort[factorBase.Count];
                    exponentVector.CopyTo(copy, 0);
                    resultVectors.Add(copy);
                    resultArguments.Add(x);
                    mut.ReleaseMutex();
                }
            }
            return exponentVector;
        }, (_) => { });
        return (resultVectors, resultArguments);
    }
    static bool isBSmooth(Int128 x, List<int> factorBase, int index, int[] shifts, ushort[] exponentVector)
    {
        Array.Clear(exponentVector);
        for (int i = 0; i < factorBase.Count; i++)
        {
            int prime = factorBase[i];
            int r = index % prime;
            int k = i << 1;
            if (r != shifts[k] && r != shifts[k + 1])
            {
                continue;
            }
            Int128 remainder = 0;
            Int128 dr = Int128.DivRem(x, prime, out remainder);
            while (remainder == 0)
            {
                x = dr;
                if (x == 1)
                {
                    exponentVector[i]++;
                    return true;
                }
                exponentVector[i]++;
                dr = Int128.DivRem(x, prime, out remainder);
            }
        }
        return x == 1;
    }
    static void sieve(byte[] interval, Int128 start, int intervalSize, List<int> factorBase, List<byte> factorBaseLogs, List<int> factorBaseRoots, int[] shifts)
    {
        Parallel.For(0, factorBase.Count, i => 
        {
            int p = factorBase[i];
            int r1 = factorBaseRoots[i];
            int r2 = p - r1;
            int t1 = (int)NumTools.ModInt128(r1 - start, p);
            int t2 = (int)NumTools.ModInt128(r2 - start, p);
            int d = t1 - t2;
            int s = i << 1;
            shifts[s] = t1;
            shifts[1 + s] = t2;
            int limit = intervalSize - Math.Max(t1, t2);
            byte log = factorBaseLogs[i];
            for (int k = t1; k < limit; k += p)
            {
                interval[k] += log;
                interval[k - d] += log;
            }
        });
    }
    static List<int> getFactorBase(Int128 n, int limit, List<int> primes)
    {
        List<int> result = new List<int>();
        int i = 1;
        while (result.Count < limit)
        {
            int prime = primes[i];
            if (NumTools.JacobiSymbolInt128(n, prime) == 1)
            {
                result.Add(prime);
            }
            i++;
        }
        return result;
    }
}
static class NumTools
{
    static List<int> primes = SegmentedSieve(100000, 10000);
    public static Int128 PrimitiveRoot(Int128 n)
    {
        if (!IsCyclic(n)) 
        {
            throw new Exception($"Primitive root modulo {n} does not exists.");
        }
        Dictionary<Int128, byte> factorization = GetFactorization(n);
        Int128 totient = Totient(n, factorization);
        Dictionary<Int128, byte> totientFactors = TotientFactors(factorization);
        Int128 result = 1;
        bool found = false;
        while (!found) 
        {
            result += 1;
            found = IsPrimitiveRoot(result, n, totient, totientFactors);
        }
        return result;
    }
    static bool IsPrimitiveRoot(Int128 root, Int128 mod, Int128 totient, Dictionary<Int128, byte> totientFactors) 
    {
        if (Int128.GreatestCommonDivisor(root, mod) != 1) 
        {
            return false;
        }
        foreach (var factor in totientFactors) 
        {
            if (Int128.ModPow(root, totient / factor.Value, mod) == 1) 
            {
                return false;
            }
        }
        return true;
    }
    public static Int128 GetMultOrder(Int128 x, Int128 mod, Dictionary<Int128, byte> modFactorization)
    {
        if (Int128.GreatestCommonDivisor(x, mod) != 1)
        {
            throw new Exception($"{x} is not coprime to {mod}");
        }
        Int128 totient = Totient(mod, modFactorization);
        Dictionary<Int128, byte> totientFactors = TotientFactors(modFactorization);
        List<Int128> totientDivisors = GetDivisors(totient, totientFactors);
        int i = 0;
        Int128 power = Int128.ModPow(x, totientDivisors[i], mod);
        while (power != 1)
        {
            i++;
            power = Int128.ModPow(x, totientDivisors[i], mod);
        }
        return totientDivisors[i];
    }
    static Dictionary<Int128, byte> TotientFactors(Dictionary<Int128, byte> factorization) 
    {
        Dictionary<Int128, byte> result = new Dictionary<Int128, byte>();
        foreach (var factor in factorization) 
        {
            Int128 prime = factor.Key;
            byte power = factor.Value;
            if (prime == 2 && power > 1) 
            {
                IncrementInt128(result, 2, (byte)(power - 1));
                continue;
            }
            Dictionary<Int128, byte> ff = GetFactorization(prime - 1);
            foreach (var totientFactor in ff) 
            {
                IncrementInt128(result, totientFactor.Key, totientFactor.Value);
            }
            if (power - 1 > 0) 
            {
                IncrementInt128(result, prime, (byte)(power - 1));
            }
        }
        return result;
    }
    public static bool IsCyclic(Int128 n) 
    {
        if (n == 1 || n == 2 || n == 4) 
        {
            return true;
        }
        return (n & 1) == 0 && n % 4 != 0 && IsPerfectPower(n, primeBase : true).Item2 != 0;
    }
    public static Int128 CarmichaelFunction(Dictionary<Int128, byte> factorization) 
    {
        List<Int128> lambdas = new List<Int128>();
        foreach (var factor in factorization) 
        {
            Int128 prime = factor.Key;
            byte power = factor.Value;
            if (prime == 2 && power > 2)
            {
                lambdas.Add((Int128)1 << (power - 2));
            }
            else 
            {
                lambdas.Add((prime - 1) * BinaryRaise128(prime, power - 1));
            }
        }
        return LCM(lambdas);
    }
    public static Int128 Totient(Int128 n, Dictionary<Int128, byte> factorization) 
    {
        Int128 result = 1;
        foreach (var factor in factorization) 
        {
            Int128 prime = factor.Key;
            byte power = factor.Value;
            result *= (prime - 1) * BinaryRaise128(prime, power - 1);
        }
        return result;
    }
    public static List<Int128> GetDivisors(Int128 n, Dictionary<Int128, byte> f)
    {
        List<Int128> result = new List<Int128>() { 1 };
        HashSet<Int128> hs = new HashSet<Int128>() { 1 };
        List<Int128> factors = new List<Int128>();
        foreach (var x in f) 
        {
            Int128 prime = x.Key;
            byte power = x.Value;
            for (int i = 0; i < power; i++) 
            {
                factors.Add(prime);
            }
        }
        for (int i = 0; i < factors.Count; i++) 
        {
            Int128 prime = factors[i];
            int count = result.Count;
            for (int j = 0; j < count; j++)
            {
                Int128 product = prime * result[j];
                if (!hs.Contains(product))
                {
                    result.Add(product);
                    hs.Add(product);
                }
            }
        }
        if (!hs.Contains(n))
        {
            result.Add(n);
        }
        result.Sort();
        return result;
    }
    public static Dictionary<Int128, byte> GetFactorization(Int128 n) 
    {
        Dictionary<Int128, byte> result = new Dictionary<Int128, byte>();
        byte t = 0;
        while ((n & 1) == 0)
        {
            t++;
            n >>= 1;
        }
        if (t > 0)
        {
            result.Add(2, t);
        }
        if (n == 1) 
        {
            return result;
        }
        Queue<Int128> queue = new Queue<Int128>();
        queue.Enqueue(n);
        while (queue.Count != 0) 
        {
            Int128 factor = queue.Dequeue();
            if (IsPrimeInt128(factor, 10)) 
            {
                IncrementInt128(result, factor, 1);
                continue;

            }
            (Int128, byte) primePower = IsPerfectPower(factor, primeBase : true);
            if (primePower.Item2 != 0) 
            {
                IncrementInt128(result, primePower.Item1, primePower.Item2);
                continue;
            }
            int factorLength = GetBitLength(factor);
            Int128 divisor = factor;
            divisor = PollardRho128(divisor, iterationLimit : 5000);
            if (divisor != factor && divisor != 1)
            {
                queue.Enqueue(divisor);
                queue.Enqueue(factor / divisor);
                continue;
            }
            int i = 0;
            var sieveConfiguration = QuadraticSieve128.sieveConfiguration;
            while (i + 1 < sieveConfiguration.Count && factorLength > sieveConfiguration[i + 1].Item1) 
            {
                i++;
            }
            (int, int, int, int) configuration = sieveConfiguration[i];
            List<Int128> divisors = QuadraticSieve128.findFactor(factor, primes, configuration.Item2, configuration.Item3, configuration.Item4);
            while (divisors.Count == 0) 
            {
                configuration.Item2 += 256;
                divisors = QuadraticSieve128.findFactor(factor, primes, configuration.Item2, configuration.Item3, configuration.Item4);
            }
            Int128 product = 1;
            for (int j = 0; j < divisors.Count; j++)
            {
                Int128 d = divisors[j];
                queue.Enqueue(d);
                product *= d;
            }
            if (product != factor)
            {
                queue.Enqueue(factor / product);
            }
        }
        return result;
    }
    static Int128 PollardRho128(Int128 n, int iterationLimit) 
    {
        Int128 x = Random.Shared.NextInt64();
        Int128 c = Random.Shared.NextInt64();
        Int128 f(Int128 a) => ((a * a + c) % n);
        Int128 y = x;
        Int128 d = 1;
        int i = 0;
        while (d == 1 && i < iterationLimit)
        {
            x = f(x);
            y = f(f(y));
            Int128 diff = x - y;
            diff *= diff.Sign;
            d = Int128.GreatestCommonDivisor(diff, n);
            i++;
        }
        return d;
    }
    static long PollardRho(long n)
    {
        long x = Random.Shared.NextInt64();
        long c = Random.Shared.NextInt64();
        long f(BigInteger a) => (long)((a * a + c) % n);
        long y = x;
        long d = 1;
        while (d == 1)
        {
            x = f(x);
            y = f(f(y));
            d = GCD(Math.Abs(x - y), n);
        }
        return d;
    }
    static Dictionary<long, byte> NaiveFactor(long n, List<int> primes)
    {
        int i = 0;
        Dictionary<long, byte> result = new Dictionary<long, byte>();
        while (n != 1)
        {
            int prime = primes[i];
            long remainder = 0;
            long divisor = DivRem(n, prime, out remainder);
            if (remainder == 0)
            {
                Increment(result, prime);
                n = divisor;
            }
            else
            {
                i++;
            }
        }
        if (n != 1) 
        {
            result.Add(n, 1);
        }
        return result;
    }
    static void IncrementInt128(Dictionary<Int128, byte> factors, Int128 prime, byte increment)
    {
        if (factors.ContainsKey(prime))
        {
            factors[prime] += increment;
        }
        else
        {
            factors.Add(prime, increment);
        }
    }
    static void Increment(Dictionary<long, byte> factors, long prime) 
    {
        if (factors.ContainsKey(prime))
        {
            factors[prime]++;
        }
        else 
        {
            factors.Add(prime, 1);
        }
    }
    public static (bool, BigInteger) ShanksTonelli(BigInteger n, BigInteger p)
    {
        n = Mod(n, p);
        if (n % p == 0)
        {
            return (true, 0);
        }
        BigInteger q = p - 1;
        int pt = 0;
        while ((q & 1) == 0)
        {
            pt++;
            q >>= 1;
        }
        int s = pt;
        if (s == 1)
        {
            return (true, BigInteger.ModPow(n, (p + 1) >> 2, p));
        }
        BigInteger z = 1;
        while (BigInteger.ModPow(z, (p - 1) >> 1, p) != p - 1)
        {
            z++;
        }
        BigInteger c = BigInteger.ModPow(z, q, p);
        BigInteger R = BigInteger.ModPow(n, (q + 1) >> 1, p);
        BigInteger t = BigInteger.ModPow(n, q, p);
        int m = s;
        while (t != 1)
        {
            int i = 0;
            while (BigInteger.ModPow(t, 1 << i, p) != 1)
            {
                i++;
            }
            BigInteger b = BigInteger.ModPow(c, 1 << (m - i - 1), p);
            m = i;
            c = (b * b) % p;
            t = (t * c) % p;
            R = (R * b) % p;
        }
        return (true, R);
    }
    public static (bool, Int128) ShanksTonelliInt128(Int128 n, Int128 p)
    {
        n = ModInt128(n, p);
        if (n % p == 0)
        {
            return (true, 0);
        }
        Int128 q = p - 1;
        int pt = 0;
        while ((q & 1) == 0)
        {
            pt++;
            q >>= 1;
        }
        int s = pt;
        if (s == 1)
        {
            return (true, Int128.ModPow(n, (p + 1) >> 2, p));
        }
        Int128 z = 1;
        while (Int128.ModPow(z, (p - 1) >> 1, p) != p - 1)
        {
            z++;
        }
        Int128 c = Int128.ModPow(z, q, p);
        Int128 R = Int128.ModPow(n, (q + 1) >> 1, p);
        Int128 t = Int128.ModPow(n, q, p);
        int m = s;
        while (t != 1)
        {
            int i = 0;
            while (Int128.ModPow(t, 1 << i, p) != 1)
            {
                i++;
            }
            Int128 b = Int128.ModPow(c, 1 << (m - i - 1), p);
            m = i;
            c = (b * b) % p;
            t = (t * c) % p;
            R = (R * b) % p;
        }
        return (true, R);
    }
    public static int JacobiSymbol(BigInteger x, BigInteger n)
    {
        x = Mod(x, n);
        if (x == 0)
        {
            return 0;
        }
        BigInteger c = 1;
        while (x != 1)
        {
            int t = 0;
            while ((x & 1) == 0)
            {
                t += 1;
                x >>= 1;
            }
            BigInteger d = t * (n * n - 1) >> 3;
            c *= 1 - ((d & 1) << 1);
            BigInteger m = x;
            d = (x - 1) * (n - 1) >> 2;
            c *= 1 - ((d & 1) << 1);
            if (x == 1)
            {
                break;
            }
            x = n % x;
            if (x == 0)
            {
                break;
            }
            n = m;
        }
        return (int)c;
    }
    public static int JacobiSymbolInt128(Int128 x, Int128 n)
    {
        x = ModInt128(x, n);
        if (x == 0)
        {
            return 0;
        }
        Int128 c = 1;
        while (x != 1)
        {
            int t = 0;
            while ((x & 1) == 0)
            {
                t += 1;
                x >>= 1;
            }
            Int128 d = t * (n * n - 1) >> 3;
            c *= 1 - ((d & 1) << 1);
            Int128 m = x;
            d = (x - 1) * (n - 1) >> 2;
            c *= 1 - ((d & 1) << 1);
            if (x == 1)
            {
                break;
            }
            x = n % x;
            if (x == 0)
            {
                break;
            }
            n = m;
        }
        return (int)c;
    }
    public static Int128 LegendreSymbol(Int128 x, Int128 mod) 
    {
        if (!IsPrimeInt128(mod, 10)) 
        {
            throw new Exception($"{mod} is not prime number.");
        }
        return Int128.ModPow(x, (mod - 1) >> 1, mod);
    }
    public static (Int128, byte) IsPerfectPower(Int128 n, bool primeBase) 
    {
        int bitLength = GetBitLength(n) - 1;
        byte i = 2;
        (Int128, byte) result = (-1, 0);
        while (i < bitLength + 1 && result.Item2 == 0) 
        {
            bool perfectPower;
            Int128 root = IntRootPerfectPowerVerif(n, i, bitLength, out perfectPower);
            result = perfectPower && !primeBase || primeBase && perfectPower && IsPrimeInt128(root, 10) ? (root, i) : (-1, 0);
            i++;
        }
        return result;
    }
    static Int128 IntRootPerfectPowerVerif(Int128 n, int k, int bitLength, out bool perfectPower) 
    {
        perfectPower = false;
        Int128 bottom = 1 << (bitLength / k);
        Int128 top = bottom << 1;
        while (top - bottom > 1) 
        {
            Int128 next = (top + bottom) >> 1;
            Int128 power = BinaryRaise128(next, k);
            perfectPower = power == n;
            bool b = power > n;
            if (b)
            {
                top = next;
            }
            else 
            {
                bottom = next;
            }
        }
        return bottom;
    }
    public static Int128 IntRoot128(Int128 n, int k)
    {
        int bitLength = GetBitLength(n) - 1;
        Int128 bottom = 1 << (bitLength / k);
        Int128 top = bottom << 1;
        while (top - bottom > 1)
        {
            Int128 next = (top + bottom) >> 1;
            bool b = BinaryRaise128(next, k) > n;
            if (b)
            {
                top = next;
            }
            else
            {
                bottom = next;
            }
        }
        return bottom;
    }
    static Int128 BinaryRaise128(Int128 baSe, int power)
    {
        Int128 result = 1;
        while (power != 0) 
        {
            if ((power & 1) == 1) 
            {
                result *= baSe;
            }
            power >>= 1;
            baSe *= baSe;
        }
        return result;
    }
    public static BigInteger FloorSquareRoot(BigInteger n)
    {
        int bitLength = (int)(n.GetBitLength());
        BigInteger bottom = new BigInteger(1) << (bitLength >> 1);
        BigInteger top = bottom << 1;
        while (top - bottom > 1)
        {
            BigInteger next = (top + bottom) >> 1;
            bool b = next * next > n;
            if (b)
            {
                top = next;
            }
            else
            {
                bottom = next;
            }
        }
        return bottom;
    }
    static BigInteger BinaryRaise(BigInteger baSe, int power)
    {
        BigInteger result = 1;
        while (power != 0)
        {
            if ((power & 1) == 1)
            {
                result *= baSe;
            }
            power >>= 1;
            baSe *= baSe;
        }
        return result;
    }
    public static int GetBitLength(Int128 n) 
    {
        ulong main;
        int result = 0;
        if (n.S1 == 0) 
        {
            main = n.S0;
        }
        else
        {
            result = 64;
            main = n.S1;
        }
        return result + 64 - BitOperations.LeadingZeroCount(main);
    }
    public static BigInteger ChineseRemainderTheorem(BigInteger[] coefficients, BigInteger[] moduli) 
    {
        BigInteger product = 1;
        BigInteger sum = 0;
        for (int i = 0; i < moduli.Length; i++) 
        {
            product *= moduli[i];
        }
        for (int i = 0; i < moduli.Length; i++) 
        {
            BigInteger modulus = moduli[i];
            BigInteger p = product / modulus;
            BigInteger c = ExtendedEuclidean(p, modulus).Item2;
            sum += coefficients[i] * c * p;
        }
        return sum % product;
    }
    public static Int128 RandomPrimeInt128(int maxByteSize, int cycles) 
    {
        BigInteger bottom = new BigInteger(RandomNumberGenerator.GetBytes(maxByteSize));
        bottom = bottom * bottom.Sign;
        bottom += 1 - (bottom & 1);
        Int128 x = new Int128(bottom);
        bool isPrime = false;
        while (!isPrime)
        {
            x += 2;
            isPrime = IsPrimeInt128(x, cycles);
        }
        return x;
    }
    public static BigInteger RandomPrime(int size, int cycles)
    {
        BigInteger bottom = new BigInteger(RandomNumberGenerator.GetBytes(size >> 3));
        bottom = bottom * bottom.Sign;
        if (bottom.IsEven)
        {
            bottom += 1;
        }
        bool isPrime = false;
        while (!isPrime)
        {
            bottom += 2;
            isPrime = IsPrime(bottom, cycles);
        }
        return bottom;
    }
    static int[] smallPrimes = new int[5] { 3, 5, 7, 11, 13 };
    public static bool IsPrimeInt128(Int128 n, int cycles)
    {
        if (n.IsEven)
        {
            return false;
        }
        bool isPrime = true;
        for (int i = 0; i < 5; i++)
        {
            isPrime = (n % smallPrimes[i]) != 0 || n == smallPrimes[i];
            if (!isPrime)
            {
                return false;
            }
        }
        return MillerRabinInt128(n, cycles);
    }

    const long easyMillerRabinTreshold = 25000000000;
    const long pseudoPrime = 3215031751;
    public static bool MillerRabinInt128(Int128 p, int cycles)
    {
        if (p == pseudoPrime)
        {
            return false;
        }
        Int128 n = p - 1;
        int i = 0;
        int t = 1;
        while (n.IsEven)
        {
            n = n >> 1;
            t++;
        }
        bool isPrime = true;
        Int128[] bases;
        if (p < easyMillerRabinTreshold)
        {
            bases = new Int128[4] { 2, 3, 5, 7 };
        }
        else
        {
            bases = new Int128[cycles];
            for (int j = 0; j < cycles; j++)
            {
                Int128 x = new Int128(Random.Shared.NextInt64());
                bases[j] = x;
            }
        }
        while (i < bases.Length && isPrime)
        {
            Int128 x = bases[i];
            if (x == p)
            {
                i++;
                continue;
            }
            if (Int128.GreatestCommonDivisor(x, p) != 1 && (x % p != 0))
            {
                return false;
            }
            Int128 y = Int128.ModPow(x, n, p);
            int k = 0;
            while (!y.IsOne && y != p - 1 && k < t)
            {
                y = Int128.Remainder(y * y, p);
                k++;
            }
            i++;
            isPrime = (k < 1) || (y == p - 1);
        }
        return isPrime;
    }
    public static bool IsPrime(BigInteger n, int cycles)
    {
        if ((n & 1) == 0)
        {
            return false;
        }
        bool isPrime = true;
        for (int i = 0; i < 5; i++)
        {
            isPrime = (n % smallPrimes[i]) != 0 || n == smallPrimes[i];
            if (!isPrime)
            {
                return false;
            }
        }
        return MillerRabin(n, cycles);
    }
    public static bool MillerRabin(BigInteger p, int cycles)
    {
        BigInteger n = p - 1;
        int i = 0;
        int t = 1;
        while (n.IsEven)
        {
            n = n >> 1;
            t++;
        }
        bool isPrime = true;
        BigInteger[] bases;
        if (p < easyMillerRabinTreshold)
        {
            bases = new BigInteger[4] { 2, 3, 5, 7 };
        }
        else
        {
            bases = new BigInteger[cycles];
            for (int j = 0; j < cycles; j++)
            {
                byte[] b = RandomNumberGenerator.GetBytes(RandomNumberGenerator.GetInt32(1, p.GetByteCount()));
                BigInteger x = new BigInteger(b);
                x *= x.Sign;
                bases[j] = x;
            }
        }
        if (p == pseudoPrime)
        {
            return false;
        }
        while (i < bases.Length && isPrime)
        {
            BigInteger x = bases[i];
            if (x == p)
            {
                i++;
                continue;
            }
            if (BigInteger.GreatestCommonDivisor(x, p) != 1 && (x % p != 0))
            {
                return false;
            }
            BigInteger y = BigInteger.ModPow(x, n, p);
            int k = 0;
            while (!y.IsOne && y != p - 1 && k < t)
            {
                y = BigInteger.Remainder(y * y, p);
                k++;
            }
            i++;
            isPrime = (k < 1) || (y == p - 1);
        }
        return isPrime;
    }
    public static Int128 ModInverse128(Int128 a, Int128 mod) 
    {
        (Int128, Int128, Int128) ext = ExtendedEuclidean128(a, mod);
        if (ext.Item1 != 1) 
        {
            throw new Exception($"Modular inverse of {a} does not exists.");
        }
        return ext.Item2;
    }
    public static (BigInteger, BigInteger, BigInteger) ExtendedEuclidean(BigInteger a, BigInteger b)
    {
        BigInteger x = 0;
        BigInteger y = 1;
        BigInteger u = 1;
        BigInteger v = 0;
        while (a != 0)
        {
            BigInteger r;
            BigInteger q = BigInteger.DivRem(b, a, out r);
            BigInteger m = x - u * q;
            BigInteger n = y - v * q;
            b = a;
            a = r;
            x = u;
            y = v;
            u = m;
            v = n;
        }
        return (b, x, y);
    }
    public static (Int128, Int128, Int128) ExtendedEuclidean128(Int128 a, Int128 b)
    {
        Int128 x = 0;
        Int128 y = 1;
        Int128 u = 1;
        Int128 v = 0;
        while (a != 0)
        {
            Int128 r;
            Int128 q = Int128.DivRem(b, a, out r);
            Int128 m = x - u * q;
            Int128 n = y - v * q;
            b = a;
            a = r;
            x = u;
            y = v;
            u = m;
            v = n;
        }
        return (b, x, y);
    }
    public static Int128 LCM(List<Int128> list) 
    {
        Int128 result = list[0];
        for (int i = 1; i < list.Count; i++) 
        {
            Int128 gcd = Int128.GreatestCommonDivisor(result, list[i]);
            Int128 product = result * list[i];
            result = product / gcd;
        }
        return result;
    }
    public static long DivRem(long dividend, long divisor, out long remainder)
    {
        long quotient = dividend / divisor;
        remainder = dividend - divisor * quotient;
        return quotient;
    }
    public static long GCD(long a, long b)
    {
        while (a != 0 && b != 0)
        {
            if (a > b)
                a %= b;
            else
                b %= a;
        }
        return a | b;
    }
    public static BigInteger Mod(BigInteger n, BigInteger m)
    {
        if (n < 0)
        {
            return (-n * (m - 1)) % m;
        }
        return n % m;
    }

    public static Int128 ModInt128(Int128 n, Int128 m) 
    {
        if (n < 0) 
        {

            return Int128.ModMul(-n, m - 1, m);
        }
        return n % m;
    }
    public static List<int> SegmentedSieve(int n, int segmentSize)
    {
        List<int> primes = EratosthenesSieve(segmentSize);
        primes.Capacity = (int)((n / Math.Log(n)) * (1 + 1.2762 / Math.Log(n)));
        int delta = segmentSize;
        bool[] segment = new bool[segmentSize];
        while (delta < n)
        {
            Array.Clear(segment);
            int min = delta + 1;
            int max = delta + min;
            int i = 1;
            int maxSqrt = (int)Math.Sqrt(max);
            while (primes[i] < maxSqrt)
            {
                int p = primes[i];
                int t = ((min % p) * (p - 1)) % p;
                for (int k = t; k < segmentSize; k += p) 
                {
                    segment[k] = true;
                }
                i++;
            }
            for (int j = 0; j < segment.Length; j += 2)
            {
                if (!segment[j])
                {
                    int p = j + min;
                    primes.Add(j + min);
                }
            }
            delta += segmentSize;
        }
        return primes;
    }
    public static List<int> EratosthenesSieve(int n)
    {
        bool[] list = new bool[n];
        List<int> result = new List<int>();
        result.Capacity = (int)((n / Math.Log(n)) * (1 + 1.2762 / Math.Log(n)));
        int p = 2;
        while (p * p < n)
        {
            while (list[p - 2])
            {
                p++;
            }
            int k = p;
            while (k < n)
            {
                k = k + p;
                if (k >= n)
                {
                    break;
                }
                list[k - 2] = true;
            }
            p++;
        }
        for (int j = 0; j < list.Length - 2; j++)
        {
            if (!list[j])
            {
                result.Add(j + 2);
            }
        }
        return result;
    }
}