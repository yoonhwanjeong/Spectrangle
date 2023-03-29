# Spectrangle

[Spectrangle](https://en.wikipedia.org/wiki/Spectrangle) is a triangular tile-based abstract strategy game invented by Alan John Fraser-Dackers, Maxwell Graham Gordon and Lester Wynne Jordan.
This is TUI implementation of the game with multiplayer support.

## Building

Run `mvn package` to build executable jar.

## Running

Execute jar with argument `server` to run server or `client` to run client.

### Leaderboard feature

Leaderboard feature is a server-side feature that keeps tracks of players' scores in MySQL database.
In order to use this feature, you need to provide MySQL connector at runtime and have database running on `localhost:3306` with username and password `root/root`.
If you want to use different address/port/username/password, change them in [Leaderboard](src/main/java/nl/utwente/leaderboard/Leaderboard.java).

## Creating your own computer player

Implement [Strategy](src/main/java/nl/utwente/game/Strategy.java) interface and initialize [ComputerPlayer](src/main/java/nl/utwente/game/ComputerPlayer.java) with your implementation in [Client](src/main/java/nl/utwente/network/Client.java).

## Creating your own feature

Implement [Feature](src/main/java/nl/utwente/network/Feature.java) interface and initialize [Server](src/main/java/nl/utwente/network/Server.java) and [Client](src/main/java/nl/utwente/network/Client.java) with your implementation.