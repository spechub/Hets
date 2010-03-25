package de.unibremen.informatik.FactProver;

import java.net.URI;

public class Prove {

	public static void main (String[] args)
	{
		if (args.length < 2)
	    {
		System.out.println("owl_fact_prover <Ontology> <Conjecture>");
		System.exit(1);
	    } 
		
		try
		{
			URI physicalURI = URI.create(args[0]);
                        URI goalURI     = URI.create(args[1]);
			FactProver prover = new FactProver(physicalURI);
                        prover.loadGoal(goalURI);
                        boolean res = prover.prove();
                        if (res)
                        {
                            System.out.println("proved");
                            System.exit(10);
                        }
		else
                        {
                            System.out.println("disproved");
                            System.exit(20);
                        }
		}
		catch (Exception e)
		{
			System.out.println(e.getMessage());
                        System.exit(1);
		}
	}
}
