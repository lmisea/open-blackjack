public class PruebaPoligonos {
    public static void main(String[] args) {
	MaquinaDeTrazados mt = new MaquinaDeTrazados(280, 300, "Prueba de poligonos", Colores.WHITE);

	int[] xPuntos = {20, 40, 50, 30, 20, 15};
	int[] yPuntos = {50, 50, 60, 80, 80, 60};
	mt.dibujarPoligono(xPuntos, yPuntos, 6);

	xPuntos = new int[]{160, 210, 260, 208};
	yPuntos = new int[]{70, 50, 73, 130};
	mt.dibujarPoligono(xPuntos, yPuntos, 4, Colores.MAGENTA);

	xPuntos = new int[]{165, 175, 270, 200, 145};
	yPuntos = new int[]{145, 150, 200, 220, 193};
	mt.dibujarPoligonoLleno(xPuntos, yPuntos, 5, Colores.DARK_GRAY);
	
	xPuntos = new int[]{85, 50, 100};
	yPuntos = new int[]{160, 240, 245};
	mt.dibujarPoligonoLleno(xPuntos, yPuntos, 3);
	
	mt.mostrar();
    }
}
