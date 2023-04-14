import java.io.Console;
import java.util.Random;
import java.util.Scanner;

import javax.lang.model.util.ElementScanner14;

import java.awt.Font;

public class BlackjackDemo {
    // Creacion de un enum con todas las posibles cartas
    enum Carta {
        AS_PICAS, DOS_PICAS, TRES_PICAS, CUATRO_PICAS,
        CINCO_PICAS, SEIS_PICAS, SIETE_PICAS, OCHO_PICAS,
        NUEVE_PICAS, DIEZ_PICAS, J_PICAS, Q_PICAS,
        K_PICAS, COMODÍN_PICAS, AS_DIAMANTE, DOS_DIAMANTE,
        TRES_DIAMANTE, CUATRO_DIAMANTE, CINCO_DIAMANTE, SEIS_DIAMANTE,
        SIETE_DIAMANTE, OCHO_DIAMANTE, NUEVE_DIAMANTE, DIEZ_DIAMANTE,
        J_DIAMANTE, Q_DIAMANTE, K_DIAMANTE, COMODÍN_DIAMANTE,
        AS_TREBOL, DOS_TREBOL, TRES_TREBOL, CUATRO_TREBOL,
        CINCO_TREBOL, SEIS_TREBOL, SIETE_TREBOL, OCHO_TREBOL,
        NUEVE_TREBOL, DIEZ_TREBOL, J_TREBOL, Q_TREBOL,
        K_TREBOL, COMODÍN_TREBOL, AS_CORAZON, DOS_CORAZON,
        TRES_CORAZON, CUATRO_CORAZON, CINCO_CORAZON, SEIS_CORAZON,
        SIETE_CORAZON, OCHO_CORAZON, NUEVE_CORAZON, DIEZ_CORAZON,
        J_CORAZON, Q_CORAZON, K_CORAZON, COMODÍN_CORAZON;

        private Carta() {
        }
    }

    /**
	 * Metodo con el que se obtendra el palo de cualquier carta
     * perteneciente al enum Carta
     */
    //@ requires carta != null;
    //@ ensures \result == "Picas" || \result == "Diamantes" || \result == "Treboles" || \result == "Corazones";
    public static /*@ pure @*/ String obtenerPaloCarta(Carta carta) {
        if (carta.ordinal() <= 13)
            return "Picas";
        else if (carta.ordinal() <= 27)
            return "Diamantes";
        else if (carta.ordinal() <= 41)
            return "Treboles";
        else
            return "Corazones";
    }

    /**
	 * Metodo con el que se obtendra el valor de cualquier carta
     * perteneciente al enum Carta
     */
    //@ requires carta != null;
    //@ ensures 0 < \result <= 11;
    public static /*@ pure @*/ int obtenerValorCarta(Carta carta) {
        if (carta.ordinal() % 14 <= 9)
            return (carta.ordinal() % 14) + 1;
        else if (carta.ordinal() % 14 <= 12)
            return 10;
        else
            return 11;
    }

    /**
	 * Metodo con el que se obtendra el nombre de cualquier carta perteneciente
     * al enum Carta. El nombre de una carta es lo que va en sus esquinas.
     */
    //@ requires carta != null;
    //@ ensures \result.equals("A") || \result.equals("J") || \result.equals("Q") || \result.equals("K") || \result.equals("Joker") || 2 <= Integer.parseInt(\result) <= 10;
    public static /*@ pure @*/ String obtenerNombreCarta(Carta carta) {
        if (carta.ordinal() % 14 == 0)
            return "A";
        else if (carta.ordinal() % 14 <= 9)
            return Integer.toString((carta.ordinal() % 14) + 1);
        else if (carta.ordinal() % 14 == 10)
            return "J";
        else if (carta.ordinal() % 14 == 11)
            return "Q";
        else if (carta.ordinal() % 14 == 12)
            return "K";
        else
            return "Joker";
    }

    /**
	 * Metodo con el que se repartira una de las 56 cartas al azar
     */
    //@ requires baraja.length == 56;
    //@ ensures (\exists int i; 0 <= i && i < baraja.length; \result == baraja[i]);
    public static /*@ pure @*/ Carta darCarta(Carta[] baraja) {
        Random carta = new Random();
        int aleatorio = carta.nextInt(56);
        //@ assert aleatorio >= 0 && aleatorio < 56 ;
        return baraja[aleatorio];
    }

    /**
	 * Metodo con el que entregara se reparten las cartas al azar
     * para la mano de cartas del crupier o del jugador
     */
    //@ requires mazo.length == 56;
	//@ requires manoCarta.length == 17 || manoCarta.length == 21;
    //@ ensures \result != null;
    //@ ensures \result.length == 17 || \result.length == 21;
	public static Carta[] repartirCartasIniciales(Carta[] manoCarta, Carta[] mazo) {
		int i = 0;
		while (i < 2) {
			manoCarta[i] = darCarta(mazo);
			i = i + 1;
		}
		return manoCarta;
	}

    /**
	 * Metodo que permite registrar el monto de la apuesta del jugador
     * para la mano actual
     */
    //@ requires credito >= 10 && credito < Integer.MAX_VALUE / 2;
    //@ requires nombre.length() > 0;
    //@ ensures 10 <= \result || \result <= credito;
    public static /*@ non_null */ int obtenerApuesta(int credito, String nombre) {
        int i = 0;
        Scanner entrada = new Scanner(System.in);
        System.out.println("");
		// Se le explica el sistema de apuestas y creditos al jugador
		System.out.println("Siempre que apuestes, se te va descontar la apuesta de tus creditos actuales mientras se este jugando la mano.");
		System.out.println("Si ganas se te devuelve la apuesta junto con su ganacia.");
		System.out.println("Si pierdes no se te devolvera la apuesta y terminaras perdiendo dinero.");
        System.out.println("");
        System.out.print(nombre + ", por favor ingresa el monto que te gustaría apostar en esta mano: ");
        int apuesta = entrada.nextInt();

        //@ maintaining 0 <= i <= 4;
        //@ maintaining (\forall int k; 0 <= k && k < i; apuesta > credito || apuesta < 10 || apuesta <= credito || apuesta >= 10 );
        //@ decreases 4 - i;
        while (i < 3) {
            if (i == 2) {
                System.out.println("Se le ha establecido la apuesta minima : 10 creditos");
                apuesta = 10;
                break;
            } else if (apuesta > credito || apuesta < 10) {
                System.out.println("Cantidad invalida. La apuesta debe ser mayor igual a 10 y menor igual al numero de creditos.");
                System.out.print(nombre + ", por favor ingresa otro monto que desees apostar: ");
                apuesta = entrada.nextInt();
                i++;
            } else if (apuesta <= credito && apuesta >= 10) {
                break;
            }
        }
        return apuesta;
    }

    /**
	 * Metodo que permite calcular el valor de la suma de las cartas de una mano
     */
    //@ requires manoCartas.length == 17 || manoCartas.length == 21;
    //@ requires 2 <= numCartasMano <= manoCartas.length;
    //@ ensures 2 <= \result || \result <= 31;
    public static /*@ pure @*/ int valorMano(/*@ non_null */ Carta /*@ non_null */[] manoCartas, int numCartasMano) {
        int puntosMano = 0;
        //@ maintaining 0 <= numCartasMano <= manoCartas.length;
        //@ maintaining (\forall int k; 0 <= k && k < numCartasMano; manoCartas[k].ordinal() % 14 >= 1 || manoCartas[k].ordinal() % 14 <= 11);
        //@ decreases numCartasMano;
        while (numCartasMano != 0) {
            numCartasMano -= 1;
            //@ assume 0 <= numCartasMano <= 21;
            //@ assume 0 <= puntosMano <= 31;
            if (manoCartas[numCartasMano].ordinal() % 14 <= 9)
                puntosMano = (manoCartas[numCartasMano].ordinal() % 14) + 1 + puntosMano;
            else if (manoCartas[numCartasMano].ordinal() % 14 <= 12)
                puntosMano = 10 + puntosMano ;
            else
                puntosMano = 11 + puntosMano;
            //@ assert puntosMano >= 2 || puntosMano <= 31;
        }
        //@ assert puntosMano >= 2 || puntosMano <= 31;
        return puntosMano;
    }

    /**
	 * Metodo que dobla la apuesta del jugador
     */
    //@ requires 10 <= credito - apuesta <= 10000;
    //@ ensures \result == 2 * apuesta;
	public static /*@ pure @*/ int doblarApuesta(int apuesta, int credito) {
        apuesta = 2 * apuesta;
        System.out.println("");
        System.out.println("Se ha doblado con exito su apuesta.");
        System.out.println("Ahora su apuesta es de: " + apuesta + " creditos.");
        System.out.println("Y el numero de creditos totales que posee ahora es: " + credito + ".");
        return apuesta;
	}

    /**
	 * Metodo con el que se le consulta al jugador si desea pedir
     * una carta adicional, plantarse, doblar su apuesta (cuando
     * sea posible) o si desea salir del juego
     */
	//@ requires nombre != null;
    //@ ensures \result == 1 || \result == 2 || \result == 3 || \result == 4;
	public static int consultarDecisionJugador(String nombre, int puntosJugador, boolean acabaDeEmpezarLaMano,
            int credito, int apuesta) {
		// Opciones del jugador
        int k = 0;
		Scanner entrada = new Scanner(System.in);
		System.out.println(nombre + ", estas son tus opciones:");
		System.out.println("(1) Recibir una carta.");
		System.out.println("(2) Plantarte.");
		System.out.println("(3) Doblar el monto de la apuesta (si el valor de tus dos primeras cartas es 9, 10 o 11).");
        System.out.println("Solo se puede doblar el monto de la apuesta si se tienen dos cartas en la mano.");
		System.out.println("(4) Salir del juego.");
		System.out.print("¿Que decides?: ");
		int decision = entrada.nextInt();

        //@ maintaining 0 <= k <= 2;
        //@ decreases 3 - k;
		while (k < 3) {
            if (k == 2) {
                System.out.print("Has alcanzado la cantidad maxima de intentos.");
                System.out.print("Por lo tanto, se seleccionara que se ha plantado.");
                decision = 2;
            } else if (decision > 0 && decision < 5 && decision != 3)
				break;
            else if (decision == 3) {
                if (puntosJugador >= 9 && puntosJugador <= 11 && acabaDeEmpezarLaMano == true && (credito - apuesta) >= 10)
                        break;
                else {
                    System.out.println("");
                    System.out.println("No se puede doblar la apuesta si no se cumplen las condiciones necesarias.");
                    System.out.println("Para doblar su apuesta, el valor de su mano debe ser 9, 10 u 11.");
                    System.out.println("Ademas, solo se puede doblar el monto de la apuesta si se tienen dos cartas en la mano.");
                    System.out.println("Y si se empezo la mano con, al menos, el doble de creditos de la apuesta actual.");
                    System.out.println("");
                    System.out.print("Por favor, escoga otra opcion:");
                    decision = entrada.nextInt();
                }
            } else {
				System.out.print(nombre + " has elegido una opcion erronea.");
				System.out.print("Por favor, escoga otra opcion:");
				decision = entrada.nextInt();
			}
			k = k + 1;
		}
		return decision;
	}

	/**
	 * Metodo que pide al jugador el nombre y presenta el juego
     */
	//@ requires true;
    //@ ensures \result != null;
	public static String mensajeBienvenida() {
		Scanner entrada = new Scanner(System.in);
		// Se le da al jugador un energico saludo de bienvenida
		System.out.println("¡Desafia a la computadora en Blackjack!");
        System.out.println("Desarrollado por Isea, Luis (19-10175) y Prieto, Jesus (19-10211).");
        System.out.println("");

		// Se le pide el nombre al usuario antes de cualquier cosa
        System.out.print("Por favor, ingrese su nombre: ");
		String nombre = entrada.nextLine();

		// Se saluda al jugador con su nombre
        System.out.println("Es un placer tenerte aqui, " + nombre + ".");
        System.out.println("");

		// Se le habla un poco del sistema de creditos
		System.out.println("Posees 100 creditos por empezar a jugar. La apuesta minima por mano son 10 creditos.");
		return nombre;
	}

	/**
	 * Metodo con el que se muestra el valor de sus cartas y la del crupier al jugador
     * a traves de la interfaz de texto
     */
	//@ requires 1 <= puntosCrupier <= 31;
	//@ requires 2 <= puntosJugador <= 31;
	public static /*@ pure @*/ void mostrarPuntuacionesPorTexto(int puntosCrupier, int puntosJugador, boolean mostrarCartasCrupier,
            Carta[] crupier) {
		System.out.println("");
		if (mostrarCartasCrupier == false) {
            puntosCrupier = obtenerValorCarta(crupier[0]);
			System.out.println("Valor de la carta descubierta del crupier: " + puntosCrupier);
        } else
			System.out.println("Valor de la mano del crupier: " + puntosCrupier);
        System.out.println("Valor de la mano del jugador: " + puntosJugador);
		System.out.println("");
	}


	/**
	 * Metodo con el que se muestra la cantidad de creditos que posee el jugador
     * y la cantidad de creditos apostados en la mano actual, a traves
     * de la interfaz de texto
     */
	//@ requires 0 <= credito <= 1000000;
	//@ requires 10 <= apuesta <= 10000;
	public static /*@ pure @*/ void mostrarCreditosPorTexto(int credito, int apuesta) {
        System.out.println("Total de creditos restantes: " + credito);
        System.out.println("Creditos apostados: " + apuesta);
		System.out.println("");
	}

	/**
	 * Metodo con el que se calcula como queda el credito disponible
     * del jugador luego de apostar, doblar su apuesta o de ganar
     * una mano
     */
	//@ requires 10 <= apuesta <= 100000;
    //@ requires 0 <= credito <= 100000;
	//@ requires 0 <= operacion <= 3;
    //@ ensures \result == (credito - apuesta) || \result == (credito + (2 * apuesta)) || \result == credito + apuesta + ((apuesta * 3) / 2) || \result == credito + apuesta;
	public static /*@ pure @*/ int calcularCreditoResultante(int apuesta, int credito, int operacion) {
		// El jugador acaba de elegir el monto de la apuesta para la mano
        // o tambien puede que el jugador acaba de doblar su apuesta
        if (operacion == 0)
            //@ assume 0 <= credito - apuesta <= 100000;
			credito = credito - apuesta;
        // El jugador hizo blackjack y recibe su ganancia con razon
        // de 3 a 2 con respecto a su apuesta
		else if (operacion == 1)
            //@ assume 0 <= credito + apuesta + ((apuesta * 3) / 2) <= 100000;
            credito = credito + apuesta + ((apuesta * 3) / 2);
        // El jugador gano la mano con una ganancia con razon de 1 a 1
        else if (operacion == 2)
            //@ assume 0 <= credito + (2 * apuesta) <= 100000;
            credito = credito + (2 * apuesta);
        // El jugador empato la mano con el crupier, se le
        // devuelve la apuesta
        else
            //@ assume 0 <= credito + apuesta <= 100000;
            credito = credito + apuesta;
		return credito;
	}

    /**
	 * Metodo que verifica si el jugador o el crupier se pasaron de 21
     */
	//@ requires 2 <= puntosJugador <= 31;
	//@ requires 2 <= puntosCrupier <= 28;
    //@ ensures \result == (puntosCrupier > 21 || puntosJugador > 21);
	public static /*@ pure @*/ boolean revisarSiSePasaronDeVeintiuno(int puntosCrupier, int puntosJugador) {
		boolean sePasaronDeVeintiuno = false;
        // O el jugador o el crupier se pasaron de 21
        // Tal vez ambos
        if (puntosCrupier > 21 || puntosJugador > 21)
			sePasaronDeVeintiuno = true;
        return sePasaronDeVeintiuno;
	}

	/**
	 * Metodo que verifica si el jugador o el crupier hicieron blackjack
     */
	//@ requires 2 <= puntosJugador <= 31;
	//@ requires 2 <= puntosCrupier <= 28;
    //@ ensures \result == (puntosCrupier == 21 || puntosJugador == 21);
	public static /*@ pure @*/ boolean revisarSiHayBlackjack(int puntosCrupier, int puntosJugador) {
		boolean siHayBlackjack = false;
        // O el jugador o el crupier hicieron blackjack
        // Tal vez ambos
        if (puntosCrupier == 21 || puntosJugador == 21)
			siHayBlackjack = true;
        return siHayBlackjack;
	}

	/**
	 * Metodo con el que se determina si el jugador gano, empatado o perdio
	 * la mano de blackjack. Se le proporciona esta informacion al jugador
     * a traves de la interfaz de texto. El metodo retorna el credito
     * resultante luego de conocer el resultado de la mano
     */
	//@ requires 10 <= apuesta <= 100000;
    //@ requires 0 <= credito < 100000;
	//@ requires 2 <= puntosJugador <= 31;
	//@ requires 2 <= puntosCrupier <= 28;
    //@ ensures credito <= \result <= credito + ((apuesta + apuesta) * (3 / 2));
	public static /*@ pure @*/ int determinarResultadoMano(int apuesta, int credito, int puntosCrupier, int puntosJugador,
            String nombre) {
        System.out.println("");
        // Tanto el crupier como el jugador hicieron blackjack
        // Esto es un empate
        if (puntosCrupier == 21 && puntosJugador == 21) {
            System.out.println("AMBOS hicieron BLACKJACK, empataron la mano.");
            System.out.println("Como ambos obtuvieron 21 puntos, se te devolvera la apuesta a tus creditos disponibles.");
			credito = calcularCreditoResultante(apuesta, credito, 3);
        // El crupier hizo blackjack
        } else if (puntosCrupier == 21) {
            System.out.println("El CRUPIER hizo BLACKJACK, obtuvo 21 puntos. Perdiste la mano");
            System.out.println("Lo siento, pero no se te devolvera el dinero de la apuesta.");
        // El jugador hizo blackjack
        } else if (puntosJugador == 21) {
            System.out.println("HICISTE BLACKJACK, obtuviste 21 puntos ¡Ganaste, " + nombre + "!");
            System.out.println("¡Felicidades! Se te devolvera la apuesta y se te entregara una ganancia en razon 3:2.");
            credito = calcularCreditoResultante(apuesta, credito, 1);

        // Ninguno de los dos hizo blackjack
        // Verificar entonces si alguno se paso de 21

        // Tanto el crupier como el jugador se pasaron de 21
        // Esto es un empate
        } else if (puntosCrupier > 21 && puntosJugador > 21) {
            System.out.println("AMBOS se PASARON de 21 puntos, empataron la mano.");
            System.out.println("Se te devolvera la apuesta a tus creditos disponibles.");
            credito = calcularCreditoResultante(apuesta, credito, 3);
        // El crupier se paso de 21
        } else if (puntosCrupier > 21) {
            System.out.println("El CRUPIER se PASO de 21 puntos ¡Ganaste, " + nombre + "!");
            System.out.println("Se te devolvera la apuesta y se te entregara una ganancia en razon 1:1.");
            credito = calcularCreditoResultante(apuesta, credito, 2);
        // El jugador se paso de 21
        } else if (puntosJugador > 21) {
            System.out.println("Te PASASTE de 21 puntos, perdiste la mano.");
            System.out.println("Lo siento, pero no se te devolvera el dinero de la apuesta.");

        // Ninguno de los dos se paso de 21
        // Verificar entonces quien quedo mas cerca de 21

        // Tanto el crupier como el jugador obtuvieron la misma cantidad de puntos
        // Esto es un empate
        } else if (puntosCrupier == puntosJugador) {
            System.out.println("AMBOS obtuvieron la MISMA puntuacion, empataron la mano.");
            System.out.println("Se te devolvera la apuesta a tus creditos disponibles.");
            credito = calcularCreditoResultante(apuesta, credito, 3);
        // El crupier quedo mas cerca de 21 que el jugador
        } else if (puntosCrupier > puntosJugador) {
            System.out.println("El CRUPIER quedo MAS CERCA de 21, perdiste la mano.");
            System.out.println("Lo siento, pero no se te devolvera el dinero de la apuesta.");
        // El jugador quedo mas de 21 puntos que el crupier
        } else if (puntosJugador > puntosCrupier) {
            System.out.println("Quedaste MAS CERCA de 21 ¡Ganaste, " + nombre + "!");
            System.out.println("Se te devolvera la apuesta y se te entregara una ganancia en razon 1:1.");
            credito = calcularCreditoResultante(apuesta, credito, 2);
        }

        return credito;
	}

	/**
	 * Metodo con el que se determina si el usuario quiere jugar otra mano.
	 * Tambien se le avisa al jugador cuando haya llegado al numero
	 * maximo de manos seguidas que puede jugar por sesion y se termina
	 * el juego
     */
    //@ requires 0 <= credito <= 1000000;
    //@ ensures \result == true || \result == false;
	public static /*@ pure @*/ boolean determinarSiSeJugaraOtraMano(int credito) {
        int k = 0;
		Scanner entrada = new Scanner(System.in);
        boolean seJugaraOtraMano = false;
        System.out.println("");
		System.out.println("Tu credito actual es: " + credito);
		System.out.println("¿Deseas jugar otro mano?");
		System.out.println("Para SI escribe 1. Para NO escribe 0.");
		System.out.print("1/0: ");
		int decisionJugador = entrada.nextInt();
        //@ maintaining 0 <= k <= 3;
        //@ maintaining (\forall int p; 0 <= p && p < k; decisionJugador != 1 || decisionJugador != 0 || decisionJugador == 1 || decisionJugador == 0);
        //@ decreases 3 - k;
		while (k < 3) {
            if (k == 2) {
                System.out.print("Has alcanzado la cantidad maxima de intentos.");
                System.out.print("Por lo tanto, se asumira que ya no desea jugar.");
                seJugaraOtraMano = false;
            } else if (decisionJugador == 0) {
                seJugaraOtraMano = false;
                break;
            } else if (decisionJugador == 1) {
                seJugaraOtraMano = true;
                break;
            } else {
                System.out.println("Ha ingresado un caracter invalido.");
                System.out.print("Por favor, ingrese 1 para jugar una nueva mano o 0 para no jugar mas: ");
                decisionJugador = entrada.nextInt();
            }
            k = k + 1;
		}
		return seJugaraOtraMano;
	}

	/**
	 * Metodo con el que se determina si el color del palo y el texto de la carta
	 * sera negro o rojo. A Picas y a Treboles se les asigna el color negro.
	 * Mientras que a Diamantas y a Corazones se les asigna el color rojo
	 */
	//@ requires (paloCarta.equals("Picas") || paloCarta.equals("Diamantes") || paloCarta.equals("Treboles") || paloCarta.equals("Corazones"));
	//@ ensures (\result == Colores.BLACK) <== (paloCarta.equals("Picas") || paloCarta.equals("Treboles"));
	//@ ensures (\result == Colores.RED) <== (paloCarta.equals("Diamantes") || paloCarta.equals("Corazones"));
	public static /*@ pure @*/ Colores determinarColorCarta(String paloCarta) {
		// Si el palo es picas o treboles, se asigna el color negro
		if (paloCarta.equals("Picas") || paloCarta.equals("Treboles"))
			return Colores.BLACK;
		// Si el palo es diamantes o corazones, se asigna el color rojo
		else
			return Colores.RED;
	}

	/**
	 * Metodo con el que se determina cuantas cartas deben ir por fila a la
	 * hora de dibujarlas en la mesa de BlackJack. El objetivo es aprovechar
	 * el espacio de la mesa y no agrupar todas las cartas en una sola fila
	 */
	//@ requires 0 <= numCartasMano <= 21;
	//@ requires poseedorMano.equals("crupier") || poseedorMano.equals("jugador");
	//@ ensures \result != null;
	//@ ensures \result instanceof int[];
	//@ ensures \result.length == 3;
	public static /*@ pure @*/ int[] getSizes(int numCartasMano, String poseedorMano) {
		int[] sizes = new int[3];
		if (poseedorMano.equals("crupier")) {
			if (numCartasMano <= 12)
				sizes[0] = numCartasMano;
			else {
				sizes[0] = 12;
				sizes[1] = numCartasMano - 12;
			}
		} else {
			if (numCartasMano <= 10)
				sizes[0] = numCartasMano;
			else if (numCartasMano <= 18) {
				sizes[0] = 10;
				sizes[1] = numCartasMano - 10;
			} else {
				sizes[0] = 10;
				sizes[1] = 8;
				sizes[2] = numCartasMano - 18;
			}
		}
		return sizes;
	}

	/**
	 * Metodo con el que dado el numero de cartas de una mano, se construye un
	 * arreglo que determina la posicion X de cada una de las cartas
	 */
	//@ requires 0 <= numCartasMano <= 21;
	//@ requires 30 <= anchoCarta <= 10000;
	//@ requires 0 < anchoMesa < Integer.MAX_VALUE;
	//@ ensures \result != null;
	//@ ensures \result instanceof int[];
	//@ ensures \result.length == numCartasMano;
	public static /*@ pure @*/ int[] posicionesManoCarta(int numCartasMano, int anchoCarta, int anchoMesa) {
		int espacio = 20;
		int bloque = anchoCarta + espacio;
		int[] posicionesXdeCartas = new int[numCartasMano];
		int i = 0;
		//@ maintaining 0 <= i <= numCartasMano;
		//@ decreases numCartasMano - i;
		while (i < numCartasMano) {
			if (numCartasMano % 2 == 0) {
				//@ assume Integer.MIN_VALUE < i - (numCartasMano / 2) < Integer.MAX_VALUE;
				int posicion = i - (numCartasMano / 2);
				//@ assume Integer.MIN_VALUE < (anchoMesa / 2) + (bloque * posicion) + (espacio / 2) < Integer.MAX_VALUE;
				posicionesXdeCartas[i] = (anchoMesa / 2) + (bloque * posicion) + (espacio / 2);
			} else {
				//@ assume Integer.MIN_VALUE < i - ((numCartasMano - 1 )/ 2) < Integer.MAX_VALUE;
				int posicion = i - ((numCartasMano - 1) / 2);
				//@ assume Integer.MIN_VALUE < (anchoMesa / 2) + (bloque * posicion) - (anchoCarta / 2) < Integer.MAX_VALUE;
				posicionesXdeCartas[i] = (anchoMesa / 2) + (bloque * posicion) - (anchoCarta / 2);
			}
			i = i + 1;
		}
		return posicionesXdeCartas;
	}

	/**
	 * Metodo con el que se dibujara una mesa de BlackJack, con un semicirculo verde
	 * que imite las mesas de BlackJack reales. Tambien se dibujaran las zonas
	 * que delimitan donde van las cartas del jugador y donde las del crupier
	 */
	//@ requires mesa != null;
	//@ requires 0 < anchoMesa <= mesa.XMAX < Integer.MAX_VALUE;
	//@ requires 0 < alturaMesa <= mesa.YMAX < Integer.MAX_VALUE;
	//@ requires 30 <= alturaCarta <= 10000;
	//@ requires 30 <= anchoCarta <= 10000;
	public static /*@ pure @*/ void dibujarMesaBlackjack(MaquinaDeTrazados mesa, int anchoMesa, int alturaMesa, int alturaCarta,
			int anchoCarta) {
		// Semicírculo verde que imita una mesa de BlackJack real con un borde oscuro
		mesa.dibujarOvaloLleno(1, -(anchoMesa / 2), anchoMesa, anchoMesa, Colores.DARK_GRAY);
		mesa.dibujarOvaloLleno(9, -(anchoMesa / 2), anchoMesa - 16, anchoMesa - 16, Colores.GREEN);

		// Dibujar la zona que delimita donde van las cartas del jugador
		mesa.dibujarOvalo(57, -(anchoMesa / 2), anchoMesa - 112, anchoMesa - 20, Colores.RED);
		int[] xPuntos = new int[] {35, 70 , anchoMesa - 35, anchoMesa - 70};
		int[] yPuntos = new int[] {-5, 258 , -5, 258};
		mesa.dibujarPoligonoLleno(xPuntos, yPuntos, 4, Colores.GREEN);
		mesa.dibujarLinea(110, 250, anchoMesa - 108, 250, Colores.RED);
		mesa.configurarFuente("SansSerif", Font.BOLD, 24);
		mesa.dibujarString("Jugador", 385, 535, Colores.RED);
		mesa.dibujarString("Jugador", anchoMesa - 487, 535, Colores.RED);

		// Dibujar la zona que delimita donde van las cartas del crupier
		int[] xPuntos2 = new int[] {85, 85 , 405, 405, anchoMesa - 405, anchoMesa - 405, anchoMesa - 85, anchoMesa - 85};
		int[] yPuntos2 = new int[] {5, 123, 123, 244, 244, 123, 123, 5};
		mesa.dibujarPoligono(xPuntos2, yPuntos2, 8, Colores.BLACK);
		mesa.dibujarString("Crupier", 280, 192, Colores.BLACK);
		mesa.dibujarString("Crupier", anchoMesa - 385, 192, Colores.BLACK);

		// Escribir BlackJack debajo del semicirculo verde
		mesa.configurarFuente("SansSerif", Font.BOLD, 38);
		mesa.dibujarString("Black", (anchoMesa / 2) - 110, alturaMesa - 95, Colores.BLACK);
		mesa.dibujarString("Jack", (anchoMesa / 2) + 10, alturaMesa - 95, Colores.RED);

		// Dibujar los cuatro palos de las cartas de blackjack centrados debajo del BlackJack central
		//@ assume 0 < (anchoMesa / 2) - 110 < Integer.MAX_VALUE;
		//@ assume 0 < alturaMesa - 100 < Integer.MAX_VALUE;
		//@ assume alturaMesa - 100 + alturaCarta < Integer.MAX_VALUE;
		dibujarPaloCarta(mesa, (anchoMesa / 2) - 110, alturaMesa - 115, alturaCarta, anchoCarta, "Picas", Colores.BLACK);
		dibujarPaloCarta(mesa, (anchoMesa / 2) - 65, alturaMesa - 115, alturaCarta, anchoCarta, "Diamantes", Colores.RED);
		dibujarPaloCarta(mesa, (anchoMesa / 2) - 20, alturaMesa - 115, alturaCarta, anchoCarta, "Treboles", Colores.BLACK);
		dibujarPaloCarta(mesa, (anchoMesa / 2) + 25, alturaMesa - 115, alturaCarta, anchoCarta, "Corazones", Colores.RED);
	}

	/**
	 * Metodo con el que se dibuja el simbolo del palo de la carta.
	 * El simbolo que se dibujara estara centrado
	 */
	//@ requires mesa != null;
	//@ requires 0 < mesa.XMAX < Integer.MAX_VALUE;
	//@ requires 0 < mesa.YMAX < Integer.MAX_VALUE;
	//@ requires 0 <= (posXdeCarta + 4) < Integer.MAX_VALUE;
	//@ requires 0 <= (posYdeCarta + 5) < Integer.MAX_VALUE;
	//@ requires 30 <= alturaCarta <= 10000;
	//@ requires 30 <= anchoCarta <= 10000;
	//@ requires (posXdeCarta + anchoCarta) < Integer.MAX_VALUE;
	//@ requires (posYdeCarta + alturaCarta) < Integer.MAX_VALUE;
	//@ requires (posXdeCarta + (anchoCarta / 2) + 25) < Integer.MAX_VALUE;
	//@ requires (posYdeCarta + (alturaCarta / 2) + 18) < Integer.MAX_VALUE;
	//@ requires paloCarta.equals("Picas") || paloCarta.equals("Diamantes") || paloCarta.equals("Treboles") || paloCarta.equals("Corazones");
	//@ requires color == Colores.BLACK || color == Colores.RED;
	public static /*@ pure @*/ void dibujarPaloCarta(MaquinaDeTrazados mesa, int posXdeCarta, int posYdeCarta,
			int alturaCarta, int anchoCarta, String paloCarta, Colores color) {
		// Dibujar el símbolo de los palos de las cartas
		if (paloCarta.equals("Picas")) {
			// Dibujar el símbolo de Picas
			int[] xPuntos1 = new int[] { posXdeCarta + (anchoCarta / 2) - 12, posXdeCarta + (anchoCarta / 2),
					posXdeCarta + (anchoCarta / 2) + 11, posXdeCarta + (anchoCarta / 2) };
			int[] yPuntos1 = new int[] { posYdeCarta + (alturaCarta / 2), posYdeCarta + (alturaCarta / 2) - 15,
					posYdeCarta + (alturaCarta / 2), posYdeCarta + (alturaCarta / 2) + 5 };
			int[] xPuntos2 = new int[] { posXdeCarta + (anchoCarta / 2) - 6, posXdeCarta + (anchoCarta / 2),
					posXdeCarta + (anchoCarta / 2) + 6 };
			int[] yPuntos2 = new int[] { posYdeCarta + (alturaCarta / 2) + 18, posYdeCarta + (alturaCarta / 2) + 12,
					posYdeCarta + (alturaCarta / 2) + 18 };
			mesa.dibujarPoligonoLleno(xPuntos1, yPuntos1, 4, color);
			mesa.dibujarPoligonoLleno(xPuntos2, yPuntos2, 3, color);
			mesa.dibujarOvaloLleno(posXdeCarta + (anchoCarta / 2) - 15, posYdeCarta + (alturaCarta / 2) - 1, 15, 15,
					color);
			mesa.dibujarOvaloLleno(posXdeCarta + (anchoCarta / 2) - 1, posYdeCarta + (alturaCarta / 2) - 1, 15, 15,
					color);

		} else if (paloCarta.equals("Diamantes")) {
			// Dibujar el símbolo de Diamantes
			int[] xPuntos = new int[] { posXdeCarta + (anchoCarta / 2) - 12, posXdeCarta + (anchoCarta / 2),
					posXdeCarta + (anchoCarta / 2) + 12, posXdeCarta + (anchoCarta / 2) };
			int[] yPuntos = new int[] { posYdeCarta + (alturaCarta / 2), posYdeCarta + (alturaCarta / 2) - 18,
					posYdeCarta + (alturaCarta / 2), posYdeCarta + (alturaCarta / 2) + 18 };
			mesa.dibujarPoligonoLleno(xPuntos, yPuntos, 4, color);

		} else if (paloCarta.equals("Treboles")) {
			// Dibujar el símbolo de Treboles
			int[] xPuntos = new int[] { posXdeCarta + (anchoCarta / 2) - 6, posXdeCarta + (anchoCarta / 2),
					posXdeCarta + (anchoCarta / 2) + 6 };
			int[] yPuntos = new int[] { posYdeCarta + (alturaCarta / 2) + 18, posYdeCarta + (alturaCarta / 2) + 12,
					posYdeCarta + (alturaCarta / 2) + 18 };
			mesa.dibujarPoligonoLleno(xPuntos, yPuntos, 3, color);
			mesa.dibujarOvaloLleno(posXdeCarta + (anchoCarta / 2) - 17, posYdeCarta + (alturaCarta / 2) - 2,
					17, 17, color);
			mesa.dibujarOvaloLleno(posXdeCarta + (anchoCarta / 2) - 1, posYdeCarta + (alturaCarta / 2) - 2,
					17, 17, color);
			mesa.dibujarOvaloLleno(posXdeCarta + (anchoCarta / 2) - 9, posYdeCarta + (alturaCarta / 2) - 15,
					17, 17, color);
			mesa.dibujarOvaloLleno(posXdeCarta + (anchoCarta / 2) - 4, posYdeCarta + (alturaCarta / 2) - 1,
					8, 8, color);

		} else if (paloCarta.equals("Corazones")) {
			// Dibujar el símbolo de Corazones
			int[] xPuntos = new int[] { posXdeCarta + (anchoCarta / 2) - 14, posXdeCarta + (anchoCarta / 2),
					posXdeCarta + (anchoCarta / 2) + 14, posXdeCarta + (anchoCarta / 2) };
			int[] yPuntos = new int[] { posYdeCarta + (alturaCarta / 2) + 1, posYdeCarta + (alturaCarta / 2) - 2,
					posYdeCarta + (alturaCarta / 2) + 1, posYdeCarta + (alturaCarta / 2) + 15 };
			mesa.dibujarPoligonoLleno(xPuntos, yPuntos, 4, color);
			mesa.dibujarOvaloLleno(posXdeCarta + (anchoCarta / 2) - 16, posYdeCarta + (alturaCarta / 2) - 12, 17, 17,
					color);
			mesa.dibujarOvaloLleno(posXdeCarta + (anchoCarta / 2) - 2, posYdeCarta + (alturaCarta / 2) - 12, 17, 17,
					color);
		}
	}

	/**
	 * Metodo con el que se dibuja la forma rectangular de la carta en un color blanco
	 * y, a su vez, se dibuja el rectangulo interior que delimita el texto de la carta.
	 * Tambien con este metodo se escribira el nombre de la carta en las esquinas superior
	 * izquierda e inferior derecha. El nombre de la carta se refiere al "A", 2, 5, "J", "K", etc
	 */
	//@ requires mesa != null;
	//@ requires 0 < mesa.XMAX < Integer.MAX_VALUE;
	//@ requires 0 < mesa.YMAX < Integer.MAX_VALUE;
	//@ requires 0 <= (posXdeCarta + 4) < Integer.MAX_VALUE;
	//@ requires 0 <= (posYdeCarta + 5) < Integer.MAX_VALUE;
	//@ requires 30 <= alturaCarta <= 10000;
	//@ requires 30 <= anchoCarta <= 10000;
	//@ requires (posXdeCarta + anchoCarta) < Integer.MAX_VALUE;
	//@ requires (posYdeCarta + alturaCarta) < Integer.MAX_VALUE;
	//@ requires (posXdeCarta + (anchoCarta / 2) + 25) < Integer.MAX_VALUE;
	//@ requires (posYdeCarta + (alturaCarta / 2) + 18) < Integer.MAX_VALUE;
	//@ requires nombreCarta.equals("A") || nombreCarta.equals("J") || nombreCarta.equals("Q") || nombreCarta.equals("K") || nombreCarta.equals("Joker") || nombreCarta.equals("2") || nombreCarta.equals("3") || nombreCarta.equals("4") || nombreCarta.equals("5") || nombreCarta.equals("6") || nombreCarta.equals("7") || nombreCarta.equals("8") || nombreCarta.equals("9") || nombreCarta.equals("10");
	//@ requires color == Colores.BLACK || color == Colores.RED;
	public static /*@ pure @*/ void dibujarCartaConNombre(MaquinaDeTrazados mesa, int posXdeCarta, int posYdeCarta,
			int alturaCarta, int anchoCarta, String nombreCarta, Colores color) {
		// Dibujar el rectángulo externo e interno de la carta
		mesa.dibujarRectanguloLleno(posXdeCarta, posYdeCarta, 72, 108, Colores.WHITE);
		mesa.dibujarRectangulo(posXdeCarta + 4, posYdeCarta + 5, anchoCarta - 10, alturaCarta - 10, Colores.DARK_GRAY);

		// Configuramos la fuente apropiadamente
		mesa.configurarFuente("SansSerif", Font.BOLD, 18);

		// Escribimos el nombre de la carta en la esquina superior izquierda
		mesa.dibujarString(nombreCarta, posXdeCarta + 11, posYdeCarta + 24, color);

		// Ahora determinamos la posicion adecuada del nombre de la carta
		// que aparecera en la esquina inferior derecha
		int posXEsqInfDerecha = posXdeCarta + anchoCarta - 24;
		int posYEsqInfDerecha = posYdeCarta + alturaCarta - 12;
		if (nombreCarta.equals("A")) {
			posXEsqInfDerecha = posXdeCarta + anchoCarta - 26;
			posYEsqInfDerecha = posYdeCarta + alturaCarta - 10;
		} else if (nombreCarta.equals("10")) {
			posXEsqInfDerecha = posXdeCarta + anchoCarta - 36;
			posYEsqInfDerecha = posYdeCarta + alturaCarta - 10;
		} else if (nombreCarta.equals("J")) {
			posXEsqInfDerecha = posXdeCarta + anchoCarta - 17;
			posYEsqInfDerecha = posYdeCarta + alturaCarta - 13;
		} else if (nombreCarta.equals("Q"))
			posXEsqInfDerecha = posXdeCarta + anchoCarta - 26;
		else if (nombreCarta.equals("K")) {
			posXEsqInfDerecha = posXdeCarta + anchoCarta - 26;
			posYEsqInfDerecha = posYdeCarta + alturaCarta - 10;
		} else if (nombreCarta.equals("Joker"))
			posXEsqInfDerecha = posXdeCarta + 11;
		else
			posYEsqInfDerecha = posYdeCarta + alturaCarta - 10;

		// Finalmente escribimos el nombre de la carta en la esquina superior derecha
		mesa.dibujarString(nombreCarta, posXEsqInfDerecha, posYEsqInfDerecha, color);
	}

	/**
	 * Metodo con el que se mostrara graficamente las cartas volteadas que vayan
	 * apareciendo en la mano del crupier
	 */
	//@ requires mesa != null;
	//@ requires 0 < mesa.XMAX < Integer.MAX_VALUE;
	//@ requires 0 < mesa.YMAX < Integer.MAX_VALUE;
	//@ requires 0 <= (posXdeCarta + 4) < Integer.MAX_VALUE;
	//@ requires 0 <= (posYdeCarta + 5) < Integer.MAX_VALUE;
	//@ requires 30 <= alturaCarta <= 10000;
	//@ requires 30 <= anchoCarta <= 10000;
	//@ requires (posXdeCarta + anchoCarta) < Integer.MAX_VALUE;
	//@ requires (posYdeCarta + alturaCarta) < Integer.MAX_VALUE;
	//@ requires (posXdeCarta + (anchoCarta / 2) + 25) < Integer.MAX_VALUE;
	//@ requires (posYdeCarta + (alturaCarta / 2) + 18) < Integer.MAX_VALUE;
	public static void dibujarCartaVolteada(MaquinaDeTrazados mesa, int posXdeCarta, int posYdeCarta,
			int alturaCarta, int anchoCarta) {
		// Dibujar el rectangulo externo e interno de la carta volteada
		Colores color = Colores.ORANGE;
		mesa.dibujarRectanguloLleno(posXdeCarta, posYdeCarta, 72, 108, Colores.DARK_GRAY);
		mesa.dibujarRectangulo(posXdeCarta + 4, posYdeCarta + 5, anchoCarta - 10, alturaCarta - 10, color);

		// Arreglos para las coordenadas de los triangulos y rombos del patron central
		int[] xPuntos1 = new int[] { posXdeCarta + (anchoCarta / 2) - 12, posXdeCarta + (anchoCarta / 2) - 1,
				posXdeCarta + (anchoCarta / 2) + 11, posXdeCarta + (anchoCarta / 2) - 1 };
		int[] yPuntos1 = new int[] { posYdeCarta + (alturaCarta / 2), posYdeCarta + (alturaCarta / 2) - 19,
				posYdeCarta + (alturaCarta / 2), posYdeCarta + (alturaCarta / 2) + 19 };
		int[] xPuntos2 = new int[] { posXdeCarta + (anchoCarta / 2) - 23, posXdeCarta + (anchoCarta / 2) - 12,
				posXdeCarta + (anchoCarta / 2) - 1 };
		int[] xPuntos3 = new int[] { posXdeCarta + (anchoCarta / 2) + 21, posXdeCarta + (anchoCarta / 2) + 10,
				posXdeCarta + (anchoCarta / 2) - 1 };
		int[] yPuntos2 = new int[] { posYdeCarta + (alturaCarta / 2) - 19, posYdeCarta + (alturaCarta / 2),
				posYdeCarta + (alturaCarta / 2) - 19 };
		int[] yPuntos3 = new int[] { posYdeCarta + (alturaCarta / 2) + 19, posYdeCarta + (alturaCarta / 2),
				posYdeCarta + (alturaCarta / 2) + 19 };
		int[] xPuntos4 = new int[] { posXdeCarta + (anchoCarta / 2) - 23, posXdeCarta + (anchoCarta / 2) - 15,
				posXdeCarta + (anchoCarta / 2) - 7, posXdeCarta + (anchoCarta / 2) - 15 };
		int[] xPuntos5 = new int[] { posXdeCarta + (anchoCarta / 2) + 23, posXdeCarta + (anchoCarta / 2) + 15,
				posXdeCarta + (anchoCarta / 2) + 7, posXdeCarta + (anchoCarta / 2) + 15 };
		int[] yPuntos4 = new int[] { posYdeCarta + (alturaCarta / 2), posYdeCarta + (alturaCarta / 2) - 8,
				posYdeCarta + (alturaCarta / 2), posYdeCarta + (alturaCarta / 2) + 8 };

		// Dibujar el patron central del reverso de las cartas
		mesa.dibujarOvaloLleno(posXdeCarta + (anchoCarta / 2) - 7, posYdeCarta + (alturaCarta / 2) - 6, 13, 13,
				color);
		mesa.dibujarOvalo(posXdeCarta + (anchoCarta / 2) - 9, posYdeCarta + (alturaCarta / 2) - 8, 17, 17,
				color);
		mesa.dibujarPoligono(xPuntos1, yPuntos1, 4, color);
		mesa.dibujarLinea(posXdeCarta + (anchoCarta / 2) - 23, posYdeCarta + (alturaCarta / 2) - 4,
				posXdeCarta + (anchoCarta / 2) + 22, posYdeCarta + (alturaCarta / 2) - 4, color);
		mesa.dibujarLinea(posXdeCarta + (anchoCarta / 2) - 27, posYdeCarta + (alturaCarta / 2),
				posXdeCarta + (anchoCarta / 2) + 25, posYdeCarta + (alturaCarta / 2), color);
		mesa.dibujarLinea(posXdeCarta + (anchoCarta / 2) - 23, posYdeCarta + (alturaCarta / 2) + 4,
				posXdeCarta + (anchoCarta / 2) + 22, posYdeCarta + (alturaCarta / 2) + 4, color);
		mesa.dibujarPoligono(xPuntos2, yPuntos2, 3, color);
		mesa.dibujarPoligono(xPuntos2, yPuntos3, 3, color);
		mesa.dibujarPoligono(xPuntos3, yPuntos2, 3, color);
		mesa.dibujarPoligono(xPuntos3, yPuntos3, 3, color);
		mesa.dibujarPoligonoLleno(xPuntos4, yPuntos4, 4, color);
		mesa.dibujarPoligonoLleno(xPuntos5, yPuntos4, 4, color);

		// Arreglos para las coordenadas de los rombos de los patrones superiores e
		// inferiores
		int[] xPuntos6 = new int[] { posXdeCarta + (anchoCarta / 2) - 17, posXdeCarta + (anchoCarta / 2) - 12,
				posXdeCarta + (anchoCarta / 2) - 7, posXdeCarta + (anchoCarta / 2) - 12 };
		int[] xPuntos7 = new int[] { posXdeCarta + (anchoCarta / 2) + 17, posXdeCarta + (anchoCarta / 2) + 12,
				posXdeCarta + (anchoCarta / 2) + 7, posXdeCarta + (anchoCarta / 2) + 12 };
		int[] yPuntos6 = new int[] { posYdeCarta + 14, posYdeCarta + 9,
				posYdeCarta + 14, posYdeCarta + 19 };
		int[] yPuntos7 = new int[] { posYdeCarta + alturaCarta - 16, posYdeCarta + alturaCarta - 21,
				posYdeCarta + alturaCarta - 16, posYdeCarta + alturaCarta - 11 };

		// Dibujar el patron superior del reverso de las cartas
		mesa.dibujarOvaloLleno(posXdeCarta + (anchoCarta / 2) - 4, posYdeCarta + 11, 7, 7,
				color);
		mesa.dibujarOvalo(posXdeCarta + (anchoCarta / 2) - 6, posYdeCarta + 9, 11, 11,
				color);
		mesa.dibujarPoligonoLleno(xPuntos6, yPuntos6, 4, color);
		mesa.dibujarPoligonoLleno(xPuntos7, yPuntos6, 4, color);

		// Dibujar el patron inferior del reverso de las cartas
		mesa.dibujarOvaloLleno(posXdeCarta + (anchoCarta / 2) - 4, posYdeCarta + alturaCarta - 19, 7, 7,
				color);
		mesa.dibujarOvalo(posXdeCarta + (anchoCarta / 2) - 6, posYdeCarta + alturaCarta - 21, 11, 11,
				color);
		mesa.dibujarPoligonoLleno(xPuntos6, yPuntos7, 4, color);
		mesa.dibujarPoligonoLleno(xPuntos7, yPuntos7, 4, color);
	}

	/**
	 * Metodo con el que se mostrara graficamente los valores de las manos
	 * del crupier y del jugador en la esquina inferior izquierda
	 */
	//@ requires mesa != null;
	//@ requires 0 < mesa.XMAX < Integer.MAX_VALUE;
	//@ requires 0 < mesa.YMAX < Integer.MAX_VALUE;
	//@ requires 0 <= alturaMesa < Integer.MAX_VALUE;
	//@ requires 1 <= valorManoCrupier <= 31;
	//@ requires 2 <= valorManoJugador <= 31;
	public static /*@ pure @*/ void mostrarPuntuaciones(MaquinaDeTrazados mesa, int alturaMesa, boolean mostrarCartasCrupier,
            int valorManoCrupier, int valorManoJugador, Carta[] crupier) {
		// Convertimos las puntuaciones de int a String para poder escribirlas
		// en la interfaz grafica
        if (mostrarCartasCrupier == false)
			valorManoCrupier = obtenerValorCarta(crupier[0]);
		String puntuacionCrupier = Integer.toString(valorManoCrupier);
		String puntuacionJugador = Integer.toString(valorManoJugador);

		// Configuramos la fuente apropiadamente
		mesa.configurarFuente("SansSerif", Font.BOLD, 22);

		// En el caso que la mano aun no haya terminado y no se hayan revelado
		// todas las cartas del crupier solamente podemos mostrar el valor
		// de la primera carta del crupier
		if (mostrarCartasCrupier == false)
			mesa.dibujarString("Valor carta visible del crupier: " + puntuacionCrupier, 30, alturaMesa - 105, Colores.BLACK);
		else
			mesa.dibujarString("Valor mano del crupier: " + puntuacionCrupier, 30, alturaMesa - 105, Colores.BLACK);

		// Finalmente mostramos el valor de la mano del jugador
		mesa.dibujarString("Valor mano del jugador: " + puntuacionJugador, 30, alturaMesa - 55, Colores.RED);
	}

	/**
	 * Metodo con el que se mostrara graficamente la cantidad de creditos
	 * que posee el jugador y la cantidad de creditos que se aposto en la mano.
	 * Estas se muestran en la esquina inferior derecha
	 */
	//@ requires mesa != null;
	//@ requires 0 < mesa.XMAX < Integer.MAX_VALUE;
	//@ requires 0 < mesa.YMAX < Integer.MAX_VALUE;
	//@ requires 0 <= alturaMesa < Integer.MAX_VALUE;
	//@ requires 0 <= anchoMesa < Integer.MAX_VALUE;
	//@ requires 0 <= credito <= 1000000;
	//@ requires 10 <= apuesta <= 10000;
	public static /*@ pure @*/ void mostrarCreditos(MaquinaDeTrazados mesa, int anchoMesa, int alturaMesa,
			int credito, int apuesta) {
		String creditosTotales = Integer.toString(credito);
		String creditosApostados = Integer.toString(apuesta);
		mesa.configurarFuente("SansSerif", Font.BOLD, 22);
		mesa.dibujarString("Total de creditos restantes: " + creditosTotales, anchoMesa - 425, alturaMesa - 105, Colores.BLACK);
		mesa.dibujarString("Creditos apostados: " + creditosApostados, anchoMesa - 325, alturaMesa - 55, Colores.RED);
	}

	//@ ensures \result != null;
	//@ ensures \result.length == 56;
	public static /*@ pure @*/ Carta[] repartirCartasEnElMazo() {
		Carta[] mazo = new Carta[] {
            Carta.AS_PICAS, Carta.DOS_PICAS, Carta.TRES_PICAS, Carta.CUATRO_PICAS,
            Carta.CINCO_PICAS, Carta.SEIS_PICAS, Carta.SIETE_PICAS, Carta.OCHO_PICAS,
            Carta.NUEVE_PICAS, Carta.DIEZ_PICAS, Carta.J_PICAS, Carta.Q_PICAS,
            Carta.K_PICAS, Carta.COMODÍN_PICAS, Carta.AS_DIAMANTE, Carta.DOS_DIAMANTE,
            Carta.TRES_DIAMANTE, Carta.CUATRO_DIAMANTE, Carta.CINCO_DIAMANTE, Carta.SEIS_DIAMANTE,
            Carta.SIETE_DIAMANTE, Carta.OCHO_DIAMANTE, Carta.NUEVE_DIAMANTE, Carta.DIEZ_DIAMANTE,
            Carta.J_DIAMANTE, Carta.Q_DIAMANTE, Carta.K_DIAMANTE, Carta.COMODÍN_DIAMANTE,
            Carta.AS_TREBOL, Carta.DOS_TREBOL, Carta.TRES_TREBOL, Carta.CUATRO_TREBOL,
            Carta.CINCO_TREBOL, Carta.SEIS_TREBOL, Carta.SIETE_TREBOL, Carta.OCHO_TREBOL,
            Carta.NUEVE_TREBOL, Carta.DIEZ_TREBOL, Carta.J_TREBOL, Carta.Q_TREBOL,
            Carta.K_TREBOL, Carta.COMODÍN_TREBOL, Carta.AS_CORAZON, Carta.DOS_CORAZON,
            Carta.TRES_CORAZON, Carta.CUATRO_CORAZON, Carta.CINCO_CORAZON, Carta.SEIS_CORAZON,
            Carta.SIETE_CORAZON, Carta.OCHO_CORAZON, Carta.NUEVE_CORAZON, Carta.DIEZ_CORAZON,
            Carta.J_CORAZON, Carta.Q_CORAZON, Carta.K_CORAZON, Carta.COMODÍN_CORAZON
        };
		return mazo;
	}

	public static void dibujarCartasCrupier(MaquinaDeTrazados mesa, int anchoMesa, int anchoCarta, int alturaCarta, int[] sizes,
			int numCartasCrupier, Carta[] crupier, boolean mostrarCartasCrupier) {
		int i = 0;
		int j = 0;
		while (i < numCartasCrupier) {
			int[] posicionesXdeCartas = new int[sizes[0]];
			int[] posicionesXdeCartas2 = new int[sizes[1]];
			posicionesXdeCartas = posicionesManoCarta(sizes[0], anchoCarta, anchoMesa);
			posicionesXdeCartas2 = posicionesManoCarta(sizes[1], anchoCarta, anchoMesa);
			String paloCarta = obtenerPaloCarta(crupier[i]);
			Colores color = determinarColorCarta(paloCarta);
			String nombreCarta = obtenerNombreCarta(crupier[i]);
			if (mostrarCartasCrupier == false) {
				if (i == 0) {
					dibujarCartaConNombre(mesa, posicionesXdeCartas[i], 10, alturaCarta, anchoCarta, nombreCarta, color);
					dibujarPaloCarta(mesa, posicionesXdeCartas[i], 10, alturaCarta, anchoCarta, paloCarta, color);
				} else if (i < 12)
					dibujarCartaVolteada(mesa, posicionesXdeCartas[i], 10, alturaCarta, anchoCarta);
				else {
					dibujarCartaVolteada(mesa, posicionesXdeCartas2[j], 128, alturaCarta, anchoCarta);
					j = j + 1;
				}
			} else {
				if (i < 12) {
					dibujarCartaConNombre(mesa, posicionesXdeCartas[i], 10, alturaCarta, anchoCarta, nombreCarta, color);
					dibujarPaloCarta(mesa, posicionesXdeCartas[i], 10, alturaCarta, anchoCarta, paloCarta, color);
				} else {
					dibujarCartaConNombre(mesa, posicionesXdeCartas2[j], 128, alturaCarta, anchoCarta, nombreCarta, color);
					dibujarPaloCarta(mesa, posicionesXdeCartas2[j], 128, alturaCarta, anchoCarta, paloCarta, color);
					j = j + 1;
				}
			}
			i = i + 1;
		}

	}

	public static void dibujarCartasJugador(MaquinaDeTrazados mesa, int anchoMesa, int anchoCarta, int alturaCarta, int[] sizes,
			int numCartasJugador, Carta[] jugador) {
		int i, j, k;
		i = j = k = 0;
		while (i < numCartasJugador) {
			int[] posicionesXdeCartas = new int[sizes[0]];
			int[] posicionesXdeCartas2 = new int[sizes[1]];
			int[] posicionesXdeCartas3 = new int[sizes[2]];
			posicionesXdeCartas = posicionesManoCarta(sizes[0], anchoCarta, anchoMesa);
			posicionesXdeCartas2 = posicionesManoCarta(sizes[1], anchoCarta, anchoMesa);
			posicionesXdeCartas3 = posicionesManoCarta(sizes[2], anchoCarta, anchoMesa);
			String paloCarta = obtenerPaloCarta(jugador[i]);
			Colores color = determinarColorCarta(paloCarta);
			String nombreCarta = obtenerNombreCarta(jugador[i]);
			if (i < 10) {
				dibujarCartaConNombre(mesa, posicionesXdeCartas[i], 256, alturaCarta, anchoCarta, nombreCarta, color);
				dibujarPaloCarta(mesa, posicionesXdeCartas[i], 256, alturaCarta, anchoCarta, paloCarta, color);
			} else if (i < 18) {
				dibujarCartaConNombre(mesa, posicionesXdeCartas2[j], 374, alturaCarta, anchoCarta, nombreCarta, color);
				dibujarPaloCarta(mesa, posicionesXdeCartas2[j], 374, alturaCarta, anchoCarta, paloCarta, color);
				j = j + 1;
			} else {
				dibujarCartaConNombre(mesa, posicionesXdeCartas3[k], 492, alturaCarta, anchoCarta, nombreCarta, color);
				dibujarPaloCarta(mesa, posicionesXdeCartas3[k], 492, alturaCarta, anchoCarta, paloCarta, color);
				k = k + 1;
			}
			i = i + 1;
		}
	}

    public static /*@ pure @*/ void mensajeDespedida(String nombre) {
        System.out.println("");
        System.out.println("Termino el juego. Ha sido un placer tenerte aqui, " + nombre + ".");
        System.out.println("Gracias por jugar y regresa pronto.");
    }

    public static void main(String[] args) {
        // Se crea un mazo con todas las 56 posibles cartas
        Carta mazo[] = new Carta[56];
		mazo = repartirCartasEnElMazo();

        // Se declaran e inicializan las variables basicas que se usaran en el programa
        Console con = System.console();
        Carta jugador[] = new Carta[21];
        Carta crupier[] = new Carta[17];
        int credito = 100;
		int apuesta, puntosJugador, puntosCrupier, numManosJugadas;
        apuesta = puntosJugador = puntosCrupier = numManosJugadas = 0;
		int numCartasCrupier = 2;
		int numCartasJugador = 2;
        boolean seJugaraOtraMano, mostrarCartasCrupier, finalizoLaMano, mostrarResultado, hayBlackjack, sePasaronDeVeintiuno, resultadoMostrado, calcularResultadoMano, terminoElTurnoDelJugador;
        seJugaraOtraMano = mostrarCartasCrupier = finalizoLaMano = mostrarResultado = resultadoMostrado = hayBlackjack = sePasaronDeVeintiuno = calcularResultadoMano = terminoElTurnoDelJugador = false;
        boolean acabaDeEmpezarLaMano = true;

        // Se especifican las dimensiones de las cartas
		int alturaCarta = 108;
		int anchoCarta = 72;
        // Se especifica la resolucion de la ventana de la interfaz grafica
		int alturaMesa = 774;
		int anchoMesa = 1278;

        // Mensaje de bienvenida donde se le pregunta el nombre al jugador
		String nombre = mensajeBienvenida();

		// Se crea el panel de la Máquina de Trazados. El color gris crea un fondo agradable
		MaquinaDeTrazados mesa = new MaquinaDeTrazados(anchoMesa, alturaMesa, "BlackJack", Colores.GRAY);

		while (credito >= 0 && numManosJugadas < 5) {
            // Empieza una mano
            if (acabaDeEmpezarLaMano == true) {
                // Se le pide al jugador que ingrese el monto de la apuesta usando su nombre
                // Tambien se le explica al jugador el sistema de creditos y apuestas
                apuesta = obtenerApuesta(credito, nombre);
                credito = calcularCreditoResultante(apuesta, credito, 0);

                // Una vez se tiene el monto que aposto el jugador, se reparten las cartas al azar
                // Pero solo la primera vez que se itera en la misma mano, sino se cambiarian
                // las cartas cuando se pida una nueva
                jugador = repartirCartasIniciales(jugador, mazo);
                crupier = repartirCartasIniciales(crupier, mazo);
            }

			// Dibujar la mesa de blackjack
			dibujarMesaBlackjack(mesa, anchoMesa, alturaMesa, alturaCarta, anchoCarta);

			// Dibujar las cartas del crupier. Mientras el jugador no se haya
            // platado, se dibuja la primera carta visible y el resto volteadas
            // Luego, cuando el jugador se planta, se dibujan todas las cartas
            // del crupier de forma visible
			int[] sizes = new int[3];
			sizes = getSizes(numCartasCrupier, "crupier");
			dibujarCartasCrupier(mesa, anchoMesa, anchoCarta, alturaCarta, sizes, numCartasCrupier, crupier, mostrarCartasCrupier);

			// Inmediatamente, se dibujan las cartas del jugador, todas visibles
			sizes = getSizes(numCartasJugador, "jugador");
			dibujarCartasJugador(mesa, anchoMesa, anchoCarta, alturaCarta, sizes, numCartasJugador, jugador);

			// Calculamos el valor de las manos del crupier y del jugador
			puntosCrupier = valorMano(crupier, numCartasCrupier);
			puntosJugador = valorMano(jugador, numCartasJugador);

			// Mostramos las puntuaciones y los creditos en la interfaz
			// grafica para informar al jugador
			mostrarPuntuaciones(mesa, alturaMesa, mostrarCartasCrupier, puntosCrupier, puntosJugador, crupier);
			mostrarCreditos(mesa, anchoMesa, alturaMesa, credito, apuesta);

			mesa.mostrar();

			// Se le muestra al jugador la informacion de la mano por la
            // interfaz de texto tambien
			mostrarPuntuacionesPorTexto(puntosCrupier, puntosJugador, mostrarCartasCrupier, crupier);
            mostrarCreditosPorTexto(credito, apuesta);

            // Si termina la mano se le muestra el resultado al jugador hasta
            // que el jugador introduzca un caracter
            if (mostrarResultado == true) {
                con.readLine("Ingrese cualquier caracter para aceptar el resultado de la mano: ");
                // Variable necesaria para mostrar las cartas del crupier
                // justo cuando termine la mano
                mostrarResultado = false;
                resultadoMostrado = true;
            }

            // Se revisa si el jugador o el crupier hicieron blackjack
            // 0 si el jugador o el crupier se pasaron de 21
            hayBlackjack = revisarSiHayBlackjack(puntosCrupier, puntosJugador);
            sePasaronDeVeintiuno = revisarSiSePasaronDeVeintiuno(puntosCrupier, puntosJugador);
            if ((hayBlackjack == true || sePasaronDeVeintiuno == true) && resultadoMostrado == false) {
                credito = determinarResultadoMano(apuesta, credito, puntosCrupier, puntosJugador, nombre);
                finalizoLaMano = mostrarCartasCrupier = mostrarResultado = true;
            }

            // Si no hubo blackjack ni se pasaron de 21, se le da a elegir
            // al jugador que hacer a continuacion
            if (sePasaronDeVeintiuno == false && hayBlackjack == false && resultadoMostrado == false) {
                // A continuacion se le solicita al jugador decidir si se planta,
                // si pide una carta adicional, si dobla su apuesta (cuando las
                // condiciones lo permiten) o si desea salir del juego
                int decisionJugador = consultarDecisionJugador(nombre, puntosJugador, acabaDeEmpezarLaMano, credito, apuesta);
                // Con el valor false de esta variable se impide que se vuelvan a repartir
                // cartas al jugador o al crupier. De esa forma es seguro pedir una nueva
                // carta, sabiendo que las anteriores seguiran siendo las mismas
                acabaDeEmpezarLaMano = false;
                if (decisionJugador == 1) {
                    jugador[numCartasJugador] = darCarta(mazo);
                    numCartasJugador = numCartasJugador + 1;
                } else if (decisionJugador == 2) {
                    mostrarCartasCrupier = finalizoLaMano = mostrarResultado = calcularResultadoMano = terminoElTurnoDelJugador = true;
                } else if (decisionJugador == 3) {
                    credito = calcularCreditoResultante(apuesta, credito, 0);
                    apuesta = doblarApuesta(apuesta, credito);
                    jugador[numCartasJugador] = darCarta(mazo);
                    numCartasJugador = numCartasJugador + 1;
                    mostrarCartasCrupier = finalizoLaMano = mostrarResultado = calcularResultadoMano = terminoElTurnoDelJugador = true;
                }
                // El jugador decidio salirse del juego
                else
                    break;

                // El crupier pedira una carta siempre de el valor de su mano
                // sea menor igual a 16
                while (terminoElTurnoDelJugador == true && puntosCrupier <= 16) {
                    crupier[numCartasCrupier] = darCarta(mazo);
                    numCartasCrupier = numCartasCrupier + 1;
                    puntosCrupier = valorMano(crupier, numCartasCrupier);
                }
            }

            // Se determina el resultado de la mano luego de plantarse o doblar la apuesta
            if (calcularResultadoMano == true) {
                credito = determinarResultadoMano(apuesta, credito, puntosCrupier, puntosJugador, nombre);
                calcularResultadoMano = false;
            }

            // Se cierra y se borra el panel de la maquina de trazados
            // Esto es para poder redibujar el panel en el caso de que el jugador
            // o el crupier hayan decidido agarrar mas cartas
			mesa.terminar();
			mesa.limpiar();

            // Cuando termina la mano se le pregunta al jugador si quiere volver
            // a jugar otra mano o si, por otro lado, prefiere salirse del juego
			if (finalizoLaMano == true && resultadoMostrado == true) {
                // El jugador alcanzo el numero maximo de manos que puede jugar en una
                // misma sesion, por ello se termina el juego
                if (credito < 10) {
                    System.out.println("");
                    System.out.println("Tienes menos creditos que la apuesta minina para una mano. Termina el juego.");
                    break;
                } else if (numManosJugadas == 4) {
                    System.out.println("");
                    System.out.println("Has alcanzado la maxima cantidad de manos jugadas por sesion.");
                    break;
                } else
                    seJugaraOtraMano = determinarSiSeJugaraOtraMano(credito);
                if (seJugaraOtraMano == true) {
                    numManosJugadas = numManosJugadas + 1;
                    numCartasCrupier = numCartasJugador = 2;
                    acabaDeEmpezarLaMano = true;
                    finalizoLaMano = mostrarCartasCrupier = mostrarResultado = resultadoMostrado = false;
                } else
                    break;
            }
		}

		// Se cierra el programa y se despide al jugador
		mensajeDespedida(nombre);
		mesa.terminar();
	}
}
