{- |

The "Persistence" folder contains a persistence layer for Hets.
The central Hets data structures like the development graph can
be written to a database. There are interfaces to SQLite and PostGreSQL.
MySQL is not supported due to technical difficulties, see <https://github.com/spechub/Hets/pull/1752#issuecomment-350380750>.

-}

module Persistence where
