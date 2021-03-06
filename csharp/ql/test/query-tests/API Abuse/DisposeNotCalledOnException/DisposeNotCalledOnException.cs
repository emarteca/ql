// semmle-extractor-options: /r:System.ComponentModel.Primitives.dll /r:${testdir}/../../../resources/assemblies/System.Data.dll /r:System.Data.Common.dll

using System;
using System.Data.SqlClient;

class Test
{

    public void Method()
    {
        // GOOD: Disposed automatically.
        using (SqlConnection c1 = new SqlConnection(""))
        {
            c1.Open();
        }

        // GOOD: Dispose called in finally
        SqlConnection c1a = null;
        try
        {
            c1a = new SqlConnection();
            c1a.Open();
        }
        finally
        {
            if (c1a != null)
            {
                c1a.Dispose();
            }
        }

        // GOOD: Close called in finally
        SqlConnection c1b = null;
        try
        {
            c1b = new SqlConnection();
            c1b.Open();
        }
        finally
        {
            if (c1b != null)
            {
                c1b.Close();
            }
        }

        // BAD: No Dispose call in case of exception
        SqlConnection c1d = new SqlConnection();
        c1d.Open();
        c1d.Dispose();

        // BAD: No Dispose call in case of exception
        SqlConnection c1e = new SqlConnection();
        Throw1(c1e);
        c1e.Dispose();

        // BAD: No Dispose call in case of exception
        SqlConnection c1f = new SqlConnection();
        Throw2(c1f);
        c1f.Dispose();

        // GOOD: using declaration
        using SqlConnection c2 = new SqlConnection("");
        c2.Open();
    }

    void Throw1(SqlConnection sc)
    {
        if (sc == null)
            throw new Exception();
    }

    SqlConnection Throw2(SqlConnection sc)
    {
        return sc == null ? throw new Exception() : sc;
    }
}

// semmle-extractor-options: /langversion:8.0
