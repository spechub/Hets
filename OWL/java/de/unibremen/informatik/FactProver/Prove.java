package de.unibremen.informatik.FactProver;

import java.net.URI;

public class Prove {

	public static void main (String[] args)
	{
		if (args.length < 1) 
	    {
		System.out.println("owl_fact <Ontology>");
		System.exit(1);
	    }
		
		try
		{
			URI physicalURI = URI.create(args[0]);
			FactProver prover = new FactProver(physicalURI);
		}
		catch (Exception e)
		{
			System.out.println(e.getMessage());
		}
	}
}
