The database output of Hets is supposed to be used as part of [Ontohub](https://github.com/ontohub/ontohub-backend).
Ontohub names some of the data type different from Hets.
This document shows how the internal data types of Hets are mapped to the database.

# Mapping of Hets-internal data types to database types

| Hets-internal  | Database |
| ------------- | ------------- |
| Logic | Language |
| sublogics | Logic |
| Syntax (IRI from `gTheorySyntax`) | Serialization |
| Comoprhism | LanguageMapping + LogicMapping |
| dependency relation of the LibEnv | Document, DocumentLink |
| (LibName, DGraph) | Document |
| Range | FileRange: The `[Pos]` list is broken down to the first and - if present - second element, interpreted as the beginning and end of the range. It is not saved at all if the list is empty. It is assumed that the path in all elements of the list is the same. |
| DGOrigin | OMSOrigin (enumeration type) |
| Conservativity | String (a table column, the `Unknown` constructor is mapped to the containing String) |
| ConsStatus | ConsStatus |
| (DGNodeLab, Node) | OMS |
| NodeName | part of OMS |
| G_theory | Split into Language, Logic, Signature, Serialization, Symbol, Sentence and associations between these |
| G_sign | Signature + SignatureSymbol (association between Signature and Symbol, telling if a Symbol is imported) |
| GMorphism | SignatureMorphism + SymbolMapping |
| ExtSign sign symbol | Signature |
| symbol | Symbol |
| Named sentence | Sentence: Axiom / OpenConjecture / CounterTheorem / Theorem |
| (Node, Node, DGLinkLab) | Mapping |

# Saving the data

The data is saved in transactions: If an error occurs during the process of saving, no data is written to the database.

### Logic Graph

The logic graph is written in a separate command (`hets --logic-graph`).
It is assumed that no logics will be removed from Hets.
Future logics will be inserted with every version of Hets, if the command is re-run on the same database.

### Development Graph

The development graph is converted to the database types as shown in the table above.
While converting, a cache is held of all the Documents, Signatures, OMS, Sentences and Symbols that have already been processed to avoid duplicates.
If a Document imports another Document, and the imported one is already present in the database, it is selected and its OMS are not saved again.
However, this sub-Document data is processed again to update the cache - only without inserting into the database.

# Parallelism

To allow for parallel analysis of Documents, mutexes are used on a PostgreSQL database ([advisory locks](https://www.postgresql.org/docs/10/static/explicit-locking.html)).

Since Documents can be imported, finding and creating a Document must occur inside a mutex.
The key of this mutex is the location of the Document.

During analysis of a Document, a Logic may need to be created because not all Logics are saved during the migration of the logic graph.
Hence, finding and creating a Logic must occur inside a mutex that uses the same key as the logic graph migration.

# Enumeration types

PostgreSQL supports enumeration types which are used by Ontohub, but the SQL library of Hets, Persistent, does not support them at this point.
[This fork of Persistent](https://github.com/eugenk/persistent/tree/add_support_for_postgresqls_enumerated_types) allows to use these on databases that do not need to be migrated by Hets.
It is a dependency of Hets that is easily built with Haskell-Stack by just using `make stack` and `make`.
